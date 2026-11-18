-- Prove2me | solution 1 for KoanaKPaths.Main.sign_determinant_fourth_moment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:19:02.004449+00:00
-- url     : https://prove2.me/submissions/a71c929a-032b-490a-9581-13bf77a0fd5c

import Definitions.Def_KoanaKPaths_Main_Estimator

open scoped BigOperators
namespace KoanaKPaths.Main.SignMoments

lemma mean_add {Ω : Type} [Fintype Ω] (f g : Ω → ℝ) :
    uniformMean (fun w => f w + g w) = uniformMean f + uniformMean g := by
  simp [uniformMean, Finset.sum_add_distrib, add_div]

lemma mean_mul {Ω : Type} [Fintype Ω] (a : ℝ) (f : Ω → ℝ) :
    uniformMean (fun w => a * f w) = a * uniformMean f := by
  simp [uniformMean, ← Finset.mul_sum, mul_div_assoc]

lemma mean_const {Ω : Type} [Fintype Ω] [Nonempty Ω] (a : ℝ) :
    uniformMean (fun _ : Ω => a) = a := by
  simp [uniformMean]

lemma mean_mono {Ω : Type} [Fintype Ω] {f g : Ω → ℝ} (h : ∀ w, f w ≤ g w) :
    uniformMean f ≤ uniformMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun w _ => h w) (by positivity)

lemma mean_sum {Ω I : Type} [Fintype Ω] [Fintype I] (f : I → Ω → ℝ) :
    uniformMean (fun w => ∑ i, f i w) = ∑ i, uniformMean (f i) := by
  simp only [uniformMean, ← Finset.sum_div]
  congr 1
  exact Finset.sum_comm


end KoanaKPaths.Main.SignMoments



open scoped BigOperators
namespace KoanaKPaths.Main.SignMoments

lemma sign_sq (b : Bool) : (sgn b : ℝ) ^ 2 = 1 := by cases b <;> norm_num [sgn]
lemma sign_not (b : Bool) : (sgn (!b) : ℝ) = -(sgn b : ℝ) := by cases b <;> norm_num [sgn]

def flipLabel {n k : ℕ} (v : Fin n) (r : Fin k) (σ : Labels n k) : Labels n k :=
  Function.update σ v (Function.update (σ v) r (!(σ v r)))

lemma flipLabel_involutive {n k : ℕ} (v : Fin n) (r : Fin k) :
    Function.Involutive (flipLabel v r) := by
  intro σ
  funext a b
  by_cases ha : a = v <;> by_cases hb : b = r <;> simp [flipLabel, ha, hb]

lemma mean_cancel {Ω : Type} [Fintype Ω] (e : Ω ≃ Ω) (f : Ω → ℝ)
    (h : ∀ w, f (e w) = -f w) : uniformMean f = 0 := by
  have hs := e.sum_comp f
  simp_rw [h, Finset.sum_neg_distrib] at hs
  have hz : ∑ w, f w = 0 := by linarith
  simp [uniformMean, hz]

def permProd {n k : ℕ} (τ : Fin k → Fin n) (σ : Labels n k) (p : Equiv.Perm (Fin k)) : ℝ :=
  ∏ j, (sgn (σ (τ j) (p j)) : ℝ)

lemma permProd_sq {n k : ℕ} (τ : Fin k → Fin n) (σ : Labels n k) (p : Equiv.Perm (Fin k)) :
    permProd τ σ p ^ 2 = 1 := by
  simp [permProd, ← Finset.prod_pow, sign_sq]

lemma permProd_flip_same {n k : ℕ} (τ : Fin k → Fin n) (hτ : Function.Injective τ)
    (σ : Labels n k) (p : Equiv.Perm (Fin k)) (j : Fin k) :
    permProd τ (flipLabel (τ j) (p j) σ) p = -permProd τ σ p := by
  classical
  have hprod :
      (∏ s ∈ Finset.univ.erase j, (sgn (flipLabel (τ j) (p j) σ (τ s) (p s)) : ℝ)) =
        ∏ s ∈ Finset.univ.erase j, (sgn (σ (τ s) (p s)) : ℝ) := by
    apply Finset.prod_congr rfl
    intro s hs
    have hsj : s ≠ j := (Finset.mem_erase.mp hs).1
    have hne : τ s ≠ τ j := fun h => hsj (hτ h)
    simp [flipLabel, hne]
  unfold permProd
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase _ (fun s => (sgn (σ (τ s) (p s)) : ℝ)) (Finset.mem_univ j), hprod]
  simp [flipLabel, sign_not]

lemma permProd_flip_other {n k : ℕ} (τ : Fin k → Fin n) (hτ : Function.Injective τ)
    (σ : Labels n k) (p q : Equiv.Perm (Fin k)) (j : Fin k) (hpq : p j ≠ q j) :
    permProd τ (flipLabel (τ j) (p j) σ) q = permProd τ σ q := by
  classical
  apply Finset.prod_congr rfl
  intro s _
  by_cases hsj : s = j
  · subst s
    simp [flipLabel, Ne.symm hpq]
  · have hne : τ s ≠ τ j := fun h => hsj (hτ h)
    simp [flipLabel, hne]

lemma permProd_orthogonal {n k : ℕ} (τ : Fin k → Fin n) (hτ : Function.Injective τ)
    (p q : Equiv.Perm (Fin k)) :
    uniformMean (fun σ : Labels n k => permProd τ σ p * permProd τ σ q) = if p = q then 1 else 0 := by
  classical
  by_cases hpq : p = q
  · subst q
    simp only [↓reduceIte, ← pow_two, permProd_sq, mean_const]
  · rw [if_neg hpq]
    have hne : ∃ j, p j ≠ q j := by
      by_contra! h
      exact hpq (Equiv.ext h)
    obtain ⟨j, hj⟩ := hne
    let e : Labels n k ≃ Labels n k :=
      ⟨flipLabel (τ j) (p j), flipLabel (τ j) (p j), flipLabel_involutive _ _, flipLabel_involutive _ _⟩
    apply mean_cancel e
    intro σ
    change permProd τ (flipLabel (τ j) (p j) σ) p *
      permProd τ (flipLabel (τ j) (p j) σ) q = _
    rw [permProd_flip_same τ hτ, permProd_flip_other τ hτ σ p q j hj]
    ring

lemma det_second {n k : ℕ} (τ : Fin k → Fin n) (hτ : Function.Injective τ) :
    uniformMean (fun σ : Labels n k => (detD σ τ : ℝ) ^ 2) = (Nat.factorial k : ℝ) := by
  classical
  have hexp (σ : Labels n k) : (detD σ τ : ℝ) =
      ∑ p : Equiv.Perm (Fin k), ((Equiv.Perm.sign p : ℤ) : ℝ) * permProd τ σ p := by
    simp [detD, Matrix.det_apply', permProd]
  have hsign (p : Equiv.Perm (Fin k)) : (((Equiv.Perm.sign p : ℤ) : ℝ)) ^ 2 = 1 := by
    have hz : (Equiv.Perm.sign p : ℤ)^2 = 1 :=
      congrArg (fun u : ℤˣ => (u : ℤ)) (Int.units_sq (Equiv.Perm.sign p))
    exact_mod_cast hz
  simp_rw [hexp, pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [mean_sum]
  simp_rw [mean_sum]
  have hterm (p q : Equiv.Perm (Fin k)) :
      uniformMean (fun σ : Labels n k =>
        (((Equiv.Perm.sign p : ℤ) : ℝ) * permProd τ σ p) *
          (((Equiv.Perm.sign q : ℤ) : ℝ) * permProd τ σ q)) = if p = q then 1 else 0 := by
    have heq : (fun σ : Labels n k =>
        (((Equiv.Perm.sign p : ℤ) : ℝ) * permProd τ σ p) *
          (((Equiv.Perm.sign q : ℤ) : ℝ) * permProd τ σ q)) =
        (fun σ => (((Equiv.Perm.sign p : ℤ) : ℝ) * ((Equiv.Perm.sign q : ℤ) : ℝ)) *
          (permProd τ σ p * permProd τ σ q)) := by funext σ; ring
    rw [heq, mean_mul, permProd_orthogonal τ hτ p q]
    split_ifs with h
    · subst q
      simpa only [mul_one, ← pow_two] using hsign p
    · simp
  simp_rw [hterm]
  simp [Fintype.card_perm]


lemma det_zero_noninjective {n k : ℕ} (τ : Fin k → Fin n)
    (hτ : ¬ Function.Injective τ) (σ : Labels n k) : detD σ τ = 0 := by
  classical
  by_contra hdet
  apply hτ
  intro a b he
  by_contra hne
  apply hdet
  apply Matrix.det_zero_of_column_eq hne
  intro r
  simp [Matrix.of_apply, he]

lemma tensor_first {n k : ℕ} (c : (Fin k → Fin n) → ℤ) (hc : IsZeroOneTensor c) :
    uniformMean (fun σ : Labels n k => (psiFrobSq c σ : ℝ)) =
      (Nat.factorial k : ℝ) * (tensorN c : ℝ) := by
  classical
  have hsq (τ : Fin k → Fin n) : (c τ)^2 = c τ := by
    rcases hc τ with h | h <;> simp [h]
  have hterm (τ : Fin k → Fin n) :
      uniformMean (fun σ : Labels n k => ((Psi c σ τ)^2 : ℤ)) =
        if Function.Injective τ then (c τ : ℝ) * (Nat.factorial k : ℝ) else 0 := by
    by_cases hτ : Function.Injective τ
    · rw [if_pos hτ]
      simp_rw [Psi, mul_pow, hsq, Int.cast_mul, Int.cast_pow]
      rw [mean_mul, det_second τ hτ]
    · simp [Psi, det_zero_noninjective τ hτ, hτ, uniformMean]
  simp_rw [psiFrobSq, Int.cast_sum]
  rw [mean_sum]
  simp_rw [hterm]
  simp only [tensorN, Int.cast_sum, Finset.sum_filter]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  split_ifs <;> ring

end KoanaKPaths.Main.SignMoments


open scoped BigOperators
noncomputable section
namespace KoanaKPaths.Main.EvenTables
attribute [local instance] Classical.propDecidable

abbrev Perm (n : ℕ) := Equiv.Perm (Fin n)
abbrev ColoredPerm (n : ℕ) :=
  {z : (Fin n → Fin 3) × Perm n // ∀ i, z.1 (z.2 i) = z.1 i}

def colorCount {n : ℕ} (c : Fin n → Fin 3) (j : Fin 3) : ℕ :=
  Fintype.card {i // c i = j}

lemma counts_sum {n : ℕ} (c : Fin n → Fin 3) :
    colorCount c 0 + colorCount c 1 + colorCount c 2 = n := by
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv c)
  rw [Fintype.card_sigma, Fintype.card_fin] at h
  simpa [Fin.sum_univ_succ, colorCount, add_assoc] using h

def blockColor (a b : ℕ) {n : ℕ} (i : Fin n) : Fin 3 :=
  if i.val < a then 0 else if i.val < a+b then 1 else 2

lemma block_zero (a b : ℕ) {n : ℕ} (i : Fin n) :
    blockColor a b i = 0 ↔ i.val < a := by
  unfold blockColor
  split_ifs <;> simp_all

lemma block_one (a b : ℕ) {n : ℕ} (i : Fin n) :
    blockColor a b i = 1 ↔ a ≤ i.val ∧ i.val < a+b := by
  unfold blockColor
  split_ifs <;> simp_all <;> omega

lemma block_two (a b : ℕ) {n : ℕ} (i : Fin n) :
    blockColor a b i = 2 ↔ a+b ≤ i.val := by
  unfold blockColor
  split_ifs <;> simp_all <;> omega

lemma block_card_zero {n a b : ℕ} (hab : a+b ≤ n) :
    Fintype.card {i : Fin n // blockColor a b i = 0} = a := by
  let e : {i : Fin n // blockColor a b i = 0} ≃ Fin a :=
    { toFun := fun i => ⟨i.val.val, (block_zero a b i.val).mp i.property⟩
      invFun := fun j => ⟨⟨j.val, by omega⟩, (block_zero a b _).mpr j.isLt⟩
      left_inv := by intro i; apply Subtype.ext; apply Fin.ext; rfl
      right_inv := by intro j; rfl }
  simpa using Fintype.card_congr e

lemma block_card_one {n a b : ℕ} (hab : a+b ≤ n) :
    Fintype.card {i : Fin n // blockColor a b i = 1} = b := by
  let e : {i : Fin n // blockColor a b i = 1} ≃ Fin b :=
    { toFun := fun i => ⟨i.val.val-a, by have := (block_one a b i.val).mp i.property; omega⟩
      invFun := fun j => ⟨⟨a+j.val, by omega⟩, (block_one a b _).mpr (by dsimp; constructor <;> omega)⟩
      left_inv := by
        intro i
        apply Subtype.ext
        apply Fin.ext
        have := (block_one a b i.val).mp i.property
        dsimp
        omega
      right_inv := by intro j; apply Fin.ext; dsimp; omega }
  simpa using Fintype.card_congr e

lemma block_card_two {n a b : ℕ} (hab : a+b ≤ n) :
    Fintype.card {i : Fin n // blockColor a b i = 2} = n-(a+b) := by
  let e : {i : Fin n // blockColor a b i = 2} ≃ Fin (n-(a+b)) :=
    { toFun := fun i => ⟨i.val.val-(a+b), by
        have := (block_two a b i.val).mp i.property
        have := i.val.isLt
        omega⟩
      invFun := fun j => ⟨⟨a+b+j.val, by omega⟩, (block_two a b _).mpr (by dsimp; omega)⟩
      left_inv := by
        intro i
        apply Subtype.ext
        apply Fin.ext
        have := (block_two a b i.val).mp i.property
        dsimp
        omega
      right_inv := by intro j; apply Fin.ext; dsimp; omega }
  simpa using Fintype.card_congr e

lemma exists_color_enum {n : ℕ} (c : Fin n → Fin 3) :
    ∃ e : Perm n, ∀ i, c (e i) = blockColor (colorCount c 0) (colorCount c 1) i := by
  classical
  let a := colorCount c 0
  let b := colorCount c 1
  have hab : a+b ≤ n := by have := counts_sum c; omega
  let g : Fin n → Fin 3 := blockColor a b
  have hcard (j : Fin 3) : Fintype.card {i // g i = j} = Fintype.card {i // c i = j} := by
    fin_cases j
    · exact block_card_zero hab
    · exact block_card_one hab
    · change Fintype.card {i : Fin n // blockColor a b i = 2} = colorCount c 2
      rw [block_card_two hab]
      have := counts_sum c
      change n - (a+b) = colorCount c 2
      omega
  let es (j : Fin 3) : {i // g i = j} ≃ {i // c i = j} := Fintype.equivOfCardEq (hcard j)
  let e : Perm n := (Equiv.sigmaFiberEquiv g).symm |>.trans
    ((Equiv.sigmaCongrRight es).trans (Equiv.sigmaFiberEquiv c))
  refine ⟨e, ?_⟩
  intro i
  exact (es (g i) ⟨i,rfl⟩).property

def colorEnum {n : ℕ} (c : Fin n → Fin 3) : Perm n := Classical.choose (exists_color_enum c)

lemma colorEnum_spec {n : ℕ} (c : Fin n → Fin 3) (i : Fin n) :
    c (colorEnum c i) = blockColor (colorCount c 0) (colorCount c 1) i :=
  Classical.choose_spec (exists_color_enum c) i

lemma colored_card_bound (n : ℕ) : Fintype.card (ColoredPerm n) ≤ n.factorial * (n+1)^2 := by
  classical
  let encode : ColoredPerm n → Perm n × Fin (n+1) × Fin (n+1) := fun z =>
    (z.val.2 * colorEnum z.val.1,
      ⟨colorCount z.val.1 0, by have := counts_sum z.val.1; omega⟩,
      ⟨colorCount z.val.1 1, by have := counts_sum z.val.1; omega⟩)
  have hinj : Function.Injective encode := by
    intro x y he
    have hp : x.val.2 * colorEnum x.val.1 = y.val.2 * colorEnum y.val.1 := congrArg Prod.fst he
    have ha : colorCount x.val.1 0 = colorCount y.val.1 0 := congrArg (fun z => z.2.1.val) he
    have hb : colorCount x.val.1 1 = colorCount y.val.1 1 := congrArg (fun z => z.2.2.val) he
    have hc : x.val.1 = y.val.1 := by
      funext j
      obtain ⟨i,hi⟩ := (x.val.2 * colorEnum x.val.1).surjective j
      rw [← hi]
      have hi' : (x.val.2 * colorEnum x.val.1) i = (y.val.2 * colorEnum y.val.1) i :=
        congrArg (fun p : Perm n => p i) hp
      calc
        x.val.1 ((x.val.2 * colorEnum x.val.1) i) =
            blockColor (colorCount x.val.1 0) (colorCount x.val.1 1) i := by
          rw [Equiv.Perm.mul_apply, x.property, colorEnum_spec x.val.1 i]
        _ = blockColor (colorCount y.val.1 0) (colorCount y.val.1 1) i := by rw [ha,hb]
        _ = y.val.1 ((y.val.2 * colorEnum y.val.1) i) := by
          rw [Equiv.Perm.mul_apply, y.property, colorEnum_spec y.val.1 i]
        _ = y.val.1 ((x.val.2 * colorEnum x.val.1) i) := by rw [hi']
    apply Subtype.ext
    apply Prod.ext hc
    rw [hc] at hp
    exact mul_right_cancel hp
  have h := Fintype.card_le_of_injective encode hinj
  simpa [Fintype.card_prod, Fintype.card_perm, pow_two, Nat.mul_assoc] using h


abbrev Triple (n : ℕ) := Perm n × Perm n × Perm n

def IsEvenTriple {n : ℕ} (t : Triple n) : Prop := ∀ i,
    (t.1 i = i ∧ t.2.1 i = t.2.2 i) ∨
    (t.2.1 i = i ∧ t.1 i = t.2.2 i) ∨
    (t.2.2 i = i ∧ t.1 i = t.2.1 i)

abbrev EvenTriple (n : ℕ) := {t : Triple n // IsEvenTriple t}

def pickColor {n : ℕ} (t : EvenTriple n) (i : Fin n) : Fin 3 :=
  if t.val.1 i = i then 0 else if t.val.2.1 i = i then 1 else 2

def joint {n : ℕ} (t : EvenTriple n) (i : Fin n) : Fin n :=
  if pickColor t i = 0 then t.val.2.1 i else t.val.1 i

lemma pick_spec {n : ℕ} (t : EvenTriple n) (i : Fin n) :
    (pickColor t i = 0 → t.val.1 i = i ∧ t.val.2.1 i = joint t i ∧ t.val.2.2 i = joint t i) ∧
    (pickColor t i = 1 → t.val.2.1 i = i ∧ t.val.1 i = joint t i ∧ t.val.2.2 i = joint t i) ∧
    (pickColor t i = 2 → t.val.2.2 i = i ∧ t.val.1 i = joint t i ∧ t.val.2.1 i = joint t i) := by
  have ht := t.property i
  by_cases hp : t.val.1 i = i
  · have hqr : t.val.2.1 i = t.val.2.2 i := by rcases ht with h | h | h <;> aesop
    simp [pickColor, joint, hp, hqr]
  · by_cases hq : t.val.2.1 i = i
    · have hpr : t.val.1 i = t.val.2.2 i := by rcases ht with h | h | h <;> aesop
      have hri : t.val.2.2 i ≠ i := fun hr => hp (hpr.trans hr)
      simp [pickColor, joint, hp, hq, hpr, hri]
    · have hr : t.val.2.2 i = i ∧ t.val.1 i = t.val.2.1 i := by
        rcases ht with h | h | h <;> aesop
      simp [pickColor, joint, hp, hq, hr.1, hr.2]

lemma color_cases (j : Fin 3) : j = 0 ∨ j = 1 ∨ j = 2 := by omega

lemma joint_injective {n : ℕ} (t : EvenTriple n) : Function.Injective (joint t) := by
  intro i j he
  have hi := pick_spec t i
  have hj := pick_spec t j
  rcases color_cases (pickColor t i) with hci | hci | hci <;>
    rcases color_cases (pickColor t j) with hcj | hcj | hcj
  all_goals simp [hci, hcj] at hi hj
  all_goals solve
    | (apply t.val.1.injective; aesop)
    | (apply t.val.2.1.injective; aesop)
    | (apply t.val.2.2.injective; aesop)

lemma joint_preserves {n : ℕ} (t : EvenTriple n) (i : Fin n) :
    pickColor t (joint t i) = pickColor t i := by
  have hi := pick_spec t i
  have hj := pick_spec t (joint t i)
  rcases color_cases (pickColor t i) with hci | hci | hci <;>
    rcases color_cases (pickColor t (joint t i)) with hcj | hcj | hcj
  all_goals try solve | simp [hci,hcj]
  all_goals simp [hci, hcj] at hi hj
  all_goals
    have he : i = joint t i := by
      solve
        | (apply t.val.1.injective; aesop)
        | (apply t.val.2.1.injective; aesop)
        | (apply t.val.2.2.injective; aesop)
    exact (congrArg (pickColor t) he).symm

def tripleEncode {n : ℕ} (t : EvenTriple n) : ColoredPerm n :=
  ⟨(pickColor t, Equiv.ofBijective (joint t)
    ⟨joint_injective t, Finite.surjective_of_injective (joint_injective t)⟩), joint_preserves t⟩

lemma recover_p {n : ℕ} (t : EvenTriple n) (i : Fin n) :
    t.val.1 i = if pickColor t i = 0 then i else joint t i := by
  have h := pick_spec t i
  rcases color_cases (pickColor t i) with hc | hc | hc <;> simp_all

lemma recover_q {n : ℕ} (t : EvenTriple n) (i : Fin n) :
    t.val.2.1 i = if pickColor t i = 1 then i else joint t i := by
  have h := pick_spec t i
  rcases color_cases (pickColor t i) with hc | hc | hc <;> simp_all

lemma recover_r {n : ℕ} (t : EvenTriple n) (i : Fin n) :
    t.val.2.2 i = if pickColor t i = 2 then i else joint t i := by
  have h := pick_spec t i
  rcases color_cases (pickColor t i) with hc | hc | hc <;> simp_all

lemma tripleEncode_injective (n : ℕ) : Function.Injective (@tripleEncode n) := by
  intro x y he
  have hc : pickColor x = pickColor y := congrArg (fun z : ColoredPerm n => z.val.1) he
  have hp : (tripleEncode x).val.2 = (tripleEncode y).val.2 := congrArg (fun z : ColoredPerm n => z.val.2) he
  have hj : joint x = joint y := by
    funext i
    exact congrArg (fun p : Perm n => p i) hp
  apply Subtype.ext
  apply Prod.ext
  · apply Equiv.ext
    intro i
    rw [recover_p, recover_p, hc, hj]
  · apply Prod.ext
    · apply Equiv.ext
      intro i
      rw [recover_q, recover_q, hc, hj]
    · apply Equiv.ext
      intro i
      rw [recover_r, recover_r, hc, hj]

lemma evenTriple_card_bound (n : ℕ) : Fintype.card (EvenTriple n) ≤ n.factorial * (n+1)^2 := by
  classical
  exact (Fintype.card_le_of_injective tripleEncode (tripleEncode_injective n)).trans (colored_card_bound n)


abbrev Quad (n : ℕ) := Perm n × Perm n × Perm n × Perm n

def IsEvenQuad {n : ℕ} (t : Quad n) : Prop := ∀ i,
    (t.1 i = t.2.1 i ∧ t.2.2.1 i = t.2.2.2 i) ∨
    (t.1 i = t.2.2.1 i ∧ t.2.1 i = t.2.2.2 i) ∨
    (t.1 i = t.2.2.2 i ∧ t.2.1 i = t.2.2.1 i)

abbrev EvenQuad (n : ℕ) := {t : Quad n // IsEvenQuad t}

def normalize {n : ℕ} (t : EvenQuad n) : Perm n × EvenTriple n :=
  (t.val.1, ⟨(t.val.1⁻¹*t.val.2.1, t.val.1⁻¹*t.val.2.2.1, t.val.1⁻¹*t.val.2.2.2), by
    intro i
    rcases t.property i with h | h | h
    · left
      constructor
      · change t.val.1.symm (t.val.2.1 i) = i
        rw [← h.1]
        exact t.val.1.symm_apply_apply i
      · change t.val.1.symm (t.val.2.2.1 i) = t.val.1.symm (t.val.2.2.2 i)
        rw [h.2]
    · right; left
      constructor
      · change t.val.1.symm (t.val.2.2.1 i) = i
        rw [← h.1]
        exact t.val.1.symm_apply_apply i
      · change t.val.1.symm (t.val.2.1 i) = t.val.1.symm (t.val.2.2.2 i)
        rw [h.2]
    · right; right
      constructor
      · change t.val.1.symm (t.val.2.2.2 i) = i
        rw [← h.1]
        exact t.val.1.symm_apply_apply i
      · change t.val.1.symm (t.val.2.1 i) = t.val.1.symm (t.val.2.2.1 i)
        rw [h.2]⟩)

lemma normalize_injective (n : ℕ) : Function.Injective (@normalize n) := by
  intro x y he
  have ha : x.val.1 = y.val.1 := congrArg (fun z : Perm n × EvenTriple n => z.1) he
  have hb : x.val.1⁻¹*x.val.2.1 = y.val.1⁻¹*y.val.2.1 :=
    congrArg (fun z : Perm n × EvenTriple n => z.2.val.1) he
  have hc : x.val.1⁻¹*x.val.2.2.1 = y.val.1⁻¹*y.val.2.2.1 :=
    congrArg (fun z : Perm n × EvenTriple n => z.2.val.2.1) he
  have hd : x.val.1⁻¹*x.val.2.2.2 = y.val.1⁻¹*y.val.2.2.2 :=
    congrArg (fun z : Perm n × EvenTriple n => z.2.val.2.2) he
  rw [ha] at hb hc hd
  apply Subtype.ext
  exact Prod.ext ha (Prod.ext (mul_left_cancel hb) (Prod.ext (mul_left_cancel hc) (mul_left_cancel hd)))

lemma evenQuad_card_bound (n : ℕ) : Fintype.card (EvenQuad n) ≤ n.factorial^2 * (n+1)^2 := by
  have h := Fintype.card_le_of_injective normalize (normalize_injective n)
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin] at h
  calc
    _ ≤ n.factorial * Fintype.card (EvenTriple n) := h
    _ ≤ n.factorial * (n.factorial*(n+1)^2) := Nat.mul_le_mul_left _ (evenTriple_card_bound n)
    _ = _ := by ring

end KoanaKPaths.Main.EvenTables


open scoped BigOperators
namespace KoanaKPaths.Main.SignMoments
attribute [local instance] Classical.propDecidable
open EvenTables

lemma singleton_of_not_paired {α : Type} (a b c d : α)
    (h : ¬ ((a=b ∧ c=d) ∨ (a=c ∧ b=d) ∨ (a=d ∧ b=c))) :
    (a≠b ∧ a≠c ∧ a≠d) ∨ (b≠a ∧ b≠c ∧ b≠d) ∨
    (c≠a ∧ c≠b ∧ c≠d) ∨ (d≠a ∧ d≠b ∧ d≠c) := by
  classical
  by_cases hab : a=b <;> by_cases hac : a=c <;> by_cases had : a=d <;>
    by_cases hbc : b=c <;> by_cases hbd : b=d <;> by_cases hcd : c=d <;> aesop

def prod4 {n k : ℕ} (τ : Fin k → Fin n) (σ : Labels n k) (t : Quad k) : ℝ :=
  permProd τ σ t.1 * permProd τ σ t.2.1 * permProd τ σ t.2.2.1 * permProd τ σ t.2.2.2

lemma prod4_zero_first {n k : ℕ} (τ : Fin k → Fin n) (hτ : Function.Injective τ)
    (p q r s : Perm k) (j : Fin k) (hpq : p j ≠ q j) (hpr : p j ≠ r j) (hps : p j ≠ s j) :
    uniformMean (fun σ : Labels n k => prod4 τ σ (p,q,r,s)) = 0 := by
  classical
  let e : Labels n k ≃ Labels n k :=
    ⟨flipLabel (τ j) (p j), flipLabel (τ j) (p j), flipLabel_involutive _ _, flipLabel_involutive _ _⟩
  apply mean_cancel e
  intro σ
  change prod4 τ (flipLabel (τ j) (p j) σ) (p,q,r,s) = _
  unfold prod4
  simp only [Prod.fst,Prod.snd]
  rw [permProd_flip_same τ hτ, permProd_flip_other τ hτ σ p q j hpq,
    permProd_flip_other τ hτ σ p r j hpr, permProd_flip_other τ hτ σ p s j hps]
  ring

lemma prod4_zero {n k : ℕ} (τ : Fin k → Fin n) (hτ : Function.Injective τ)
    (t : Quad k) (ht : ¬ IsEvenQuad t) :
    uniformMean (fun σ : Labels n k => prod4 τ σ t) = 0 := by
  classical
  obtain ⟨j,hj⟩ : ∃ j, ¬ ((t.1 j=t.2.1 j ∧ t.2.2.1 j=t.2.2.2 j) ∨
      (t.1 j=t.2.2.1 j ∧ t.2.1 j=t.2.2.2 j) ∨
      (t.1 j=t.2.2.2 j ∧ t.2.1 j=t.2.2.1 j)) := by
    simpa only [IsEvenQuad, not_forall] using ht
  rcases singleton_of_not_paired _ _ _ _ hj with h | h | h | h
  · exact prod4_zero_first τ hτ t.1 t.2.1 t.2.2.1 t.2.2.2 j h.1 h.2.1 h.2.2
  · have hz := prod4_zero_first τ hτ t.2.1 t.1 t.2.2.1 t.2.2.2 j h.1 h.2.1 h.2.2
    convert hz using 1
    congr 1
    funext σ
    unfold prod4
    ring
  · have hz := prod4_zero_first τ hτ t.2.2.1 t.1 t.2.1 t.2.2.2 j h.1 h.2.1 h.2.2
    convert hz using 1
    congr 1
    funext σ
    unfold prod4
    ring
  · have hz := prod4_zero_first τ hτ t.2.2.2 t.1 t.2.1 t.2.2.1 j h.1 h.2.1 h.2.2
    convert hz using 1
    congr 1
    funext σ
    unfold prod4
    ring

def signCoeff {k : ℕ} (p : Perm k) : ℝ := ((Equiv.Perm.sign p : ℤ) : ℝ)

def coeff4 {k : ℕ} (t : Quad k) : ℝ :=
  signCoeff t.1 * signCoeff t.2.1 * signCoeff t.2.2.1 * signCoeff t.2.2.2

lemma signCoeff_sq {k : ℕ} (p : Perm k) : signCoeff p ^ 2 = 1 := by
  have hz : (Equiv.Perm.sign p : ℤ)^2 = 1 :=
    congrArg (fun u : ℤˣ => (u : ℤ)) (Int.units_sq (Equiv.Perm.sign p))
  unfold signCoeff
  exact_mod_cast hz

lemma coeff_prod_bound {n k : ℕ} (τ : Fin k → Fin n) (σ : Labels n k) (t : Quad k) :
    coeff4 t * prod4 τ σ t ≤ 1 := by
  have h : (coeff4 t * prod4 τ σ t)^2 = 1 := by
    simp only [coeff4,prod4,mul_pow,signCoeff_sq,permProd_sq,one_mul]
  nlinarith [sq_nonneg (coeff4 t * prod4 τ σ t - 1)]

lemma fourth_expand {n k : ℕ} (τ : Fin k → Fin n) (σ : Labels n k) :
    (detD σ τ : ℝ)^4 = ∑ t : Quad k, coeff4 t * prod4 τ σ t := by
  classical
  have hexp : (detD σ τ : ℝ) = ∑ p : Perm k, signCoeff p * permProd τ σ p := by
    simp [detD, Matrix.det_apply', permProd, signCoeff]
  rw [hexp]
  let f : Perm k → ℝ := fun p => signCoeff p * permProd τ σ p
  change (∑ p, f p)^4 = _
  symm
  calc
    _ = ∑ t : Quad k, f t.1 * f t.2.1 * f t.2.2.1 * f t.2.2.2 := by
      apply Finset.sum_congr rfl
      intro t _
      unfold coeff4 prod4 f
      ring
    _ = (∑ p, f p)^4 := by
      simp only [Fintype.sum_prod_type]
      simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
      ring

lemma det_fourth_le_even_count {n k : ℕ} (τ : Fin k → Fin n) (hτ : Function.Injective τ) :
    uniformMean (fun σ : Labels n k => (detD σ τ : ℝ)^4) ≤ (Fintype.card (EvenQuad k) : ℝ) := by
  classical
  simp_rw [fourth_expand]
  rw [mean_sum]
  calc
    _ ≤ ∑ t : Quad k, if IsEvenQuad t then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro t _
      by_cases ht : IsEvenQuad t
      · rw [if_pos ht]
        exact (mean_mono (fun σ => coeff_prod_bound τ σ t)).trans_eq (mean_const 1)
      · rw [if_neg ht, mean_mul, prod4_zero τ hτ t ht, mul_zero]
    _ = _ := by simp [Fintype.card_subtype, EvenQuad]

lemma even_count_final (k : ℕ) (hk : 1 ≤ k) :
    (Fintype.card (EvenQuad k) : ℝ) ≤ (Nat.factorial k : ℝ)^2*(k : ℝ)^3 := by
  classical
  by_cases hl : 3 ≤ k
  · have hcount : (Fintype.card (EvenQuad k) : ℝ) ≤ (Nat.factorial k : ℝ)^2*(k+1 : ℝ)^2 := by
      exact_mod_cast evenQuad_card_bound k
    have hl' : (3 : ℝ) ≤ k := by exact_mod_cast hl
    have hpoly : ((k : ℝ)+1)^2 ≤ (k : ℝ)^3 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hl') (sq_nonneg (k : ℝ)), sq_nonneg ((k : ℝ)-1)]
    exact hcount.trans (mul_le_mul_of_nonneg_left hpoly (sq_nonneg _))
  · have hcount : Fintype.card (EvenQuad k) ≤ (Nat.factorial k)^4 := by
      have h := Fintype.card_subtype_le (@IsEvenQuad k)
      simpa [Fintype.card_prod,Fintype.card_perm,pow_succ,Nat.mul_assoc] using h
    have hr : (Fintype.card (EvenQuad k) : ℝ) ≤ (Nat.factorial k : ℝ)^4 := by exact_mod_cast hcount
    have hs : k = 1 ∨ k = 2 := by omega
    rcases hs with h | h <;> subst k <;> norm_num at * <;> linarith

lemma det_fourth {n k : ℕ} (hk : 1 ≤ k) (τ : Fin k → Fin n) (hτ : Function.Injective τ) :
    uniformMean (fun σ : Labels n k => (detD σ τ : ℝ)^4) ≤
      (Nat.factorial k : ℝ)^2*(k : ℝ)^3 :=
  (det_fourth_le_even_count τ hτ).trans (even_count_final k hk)

end KoanaKPaths.Main.SignMoments

theorem solution (n k : ℕ) (hk : 1 ≤ k)
    (τ : Fin k → Fin n) (hτ : Function.Injective τ) :
    KoanaKPaths.Main.uniformMean (fun σ : KoanaKPaths.Main.Labels n k =>
      (KoanaKPaths.Main.detD σ τ : ℝ)^4) ≤
      (Nat.factorial k : ℝ)^2 * (k : ℝ)^3 := by
  exact KoanaKPaths.Main.SignMoments.det_fourth hk τ hτ
