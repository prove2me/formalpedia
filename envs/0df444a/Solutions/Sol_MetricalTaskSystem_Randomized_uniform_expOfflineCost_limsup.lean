-- Prove2me | solution 1 for MetricalTaskSystem.Randomized.uniform_expOfflineCost_limsup
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T22:22:57.324522+00:00
-- url     : https://prove2.me/submissions/227ec186-9046-45b5-8288-bafda8ca805f

import Definitions.Def_MetricalTaskSystem_Randomized_Model
import Definitions.Def_MetricalTaskSystem_Randomized_TaskDistribution

open MetricalTaskSystem.Randomized
open MeasureTheory Filter
open scoped ENNReal

private lemma integral_uniformStateSeq_fin {S : Type} [Fintype S] [Nonempty S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (j : ℕ) (g : (Fin j → S) → ℝ) :
    ∫ ω, g (fun i : Fin j => ω i) ∂(uniformStateSeq S) =
      ((Fintype.card S : ℝ)⁻¹ ^ j) * ∑ v : (Fin j → S), g v := by
  let μ₀ : Measure S := (PMF.uniformOfFintype S).toMeasure
  let I : Finset ℕ := Finset.range j
  let equivRange : (I → S) ≃ (Fin j → S) :=
    { toFun := fun y i => y ⟨i.val, Finset.mem_range.mpr i.isLt⟩
      invFun := fun v k => v ⟨k.val, Finset.mem_range.mp k.2⟩
      left_inv := fun y => by ext k; rfl
      right_inv := fun v => by ext i; rfl }
  have hcongr : (fun ω : ℕ → S => g (fun i : Fin j => ω i)) =
      (fun ω : ℕ → S => g (equivRange (I.restrict ω))) := rfl
  rw [hcongr]
  change (∫ ω : ℕ → S, (fun y : I → S => g (equivRange y)) (I.restrict ω)
    ∂Measure.infinitePi (fun _ : ℕ => μ₀)) = _
  have hmeas : AEStronglyMeasurable (fun y : I → S => g (equivRange y))
      (Measure.pi (fun _ : I => μ₀)) :=
    (Measurable.of_discrete (f := fun y : I → S => g (equivRange y))).aestronglyMeasurable
  rw [integral_restrict_infinitePi (fun _ : ℕ => μ₀) hmeas]
  rw [integral_fintype (Integrable.of_finite)]
  have hreal_singleton : ∀ y : I → S,
      (Measure.pi (fun _ : I => μ₀)).real {y} = ((Fintype.card S : ℝ)⁻¹) ^ j := by
    intro y
    unfold Measure.real
    have hsing : ({y} : Set (I → S)) = Set.univ.pi (fun i : I => {y i}) :=
      (Set.univ_pi_singleton y).symm
    rw [hsing, Measure.pi_pi]
    have hμ₀ : ∀ i : I, μ₀ {y i} = (Fintype.card S : ℝ≥0∞)⁻¹ := by
      intro i
      dsimp [μ₀]
      rw [PMF.toMeasure_apply_singleton _ (y i) (measurableSet_singleton (y i)),
          PMF.uniformOfFintype_apply]
    simp_rw [hμ₀]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, Finset.card_range,
        ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  simp_rw [smul_eq_mul, hreal_singleton, ← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp equivRange g

private def snocFun {S : Type} {k : ℕ} (v : Fin k → S) (x : S) (i : Fin (k + 1)) : S :=
  if h : i.val < k then v ⟨i.val, h⟩ else x

private def snocEquiv {S : Type} (k : ℕ) : (Fin k → S) × S ≃ (Fin (k + 1) → S) where
  toFun p := snocFun p.1 p.2
  invFun w := (fun i => w i.castSucc, w (Fin.last k))
  left_inv := by
    rintro ⟨v, x⟩
    ext i
    · simp [snocFun, i.isLt]
    · simp [snocFun, Fin.last]
  right_inv := by
    intro w
    ext i
    dsimp [snocFun]
    split_ifs with h
    · rfl
    · have hi : i = Fin.last k := Fin.ext (by dsimp [Fin.last]; omega)
      rw [hi]

private lemma sum_notMem_finset {S : Type} [Fintype S] [DecidableEq S] (A : Finset S) :
    (∑ x : S, (if x ∉ A then (1 : ℝ) else 0)) = (Fintype.card S : ℝ) - (A.card : ℝ) := by
  have h1 : ∀ x : S, (if x ∉ A then (1 : ℝ) else 0) = 1 - (if x ∈ A then (1 : ℝ) else 0) := by
    intro x
    by_cases hx : x ∈ A <;> simp [hx]
  simp_rw [h1]
  rw [Finset.sum_sub_distrib]
  simp [Finset.sum_const, Finset.card_univ]

private lemma sum_div_sub_eq_mul_harmonic (n : ℕ) :
    ∑ r ∈ Finset.range n, (n : ℝ) / ((n : ℝ) - (r : ℝ)) =
      (n : ℝ) * (harmonic n : ℝ) := by
  have hreflect := Finset.sum_range_reflect (fun m : ℕ => (n : ℝ) / ((m + 1 : ℕ) : ℝ)) n
  have hcongr : ∑ r ∈ Finset.range n, (n : ℝ) / ((n : ℝ) - (r : ℝ)) =
      ∑ r ∈ Finset.range n, (n : ℝ) / ((n - 1 - r + 1 : ℕ) : ℝ) := by
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr_lt : r < n := Finset.mem_range.mp hr
    have hnat : n - 1 - r + 1 = n - r := by omega
    rw [hnat, Nat.cast_sub (le_of_lt hr_lt)]
  rw [hcongr, hreflect]
  unfold harmonic
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

private def stepSet {S : Type} [Fintype S] [DecidableEq S] (A : Finset S) (x : S) : Finset S :=
  if insert x A = Finset.univ then ∅ else insert x A

private lemma stepSet_neg {S : Type} [Fintype S] [DecidableEq S] {A : Finset S} {x : S}
    (h : insert x A ≠ Finset.univ) : stepSet A x = insert x A := if_neg h

private def stepHit {S : Type} [Fintype S] [DecidableEq S] (A : Finset S) (x : S) : ℝ :=
  if insert x A = Finset.univ then 1 else 0

private lemma stepHit_pos {S : Type} [Fintype S] [DecidableEq S] {A : Finset S} {x : S}
    (h : insert x A = Finset.univ) : stepHit A x = 1 := if_pos h

private lemma stepHit_neg {S : Type} [Fintype S] [DecidableEq S] {A : Finset S} {x : S}
    (h : insert x A ≠ Finset.univ) : stepHit A x = 0 := if_neg h

private lemma card_stepSet_lt {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (A : Finset S) (x : S) :
    (stepSet A x).card < Fintype.card S := by
  unfold stepSet
  split_ifs with h
  · simp [Fintype.card_pos]
  · have hle : (insert x A).card ≤ Fintype.card S := Finset.card_le_univ _
    have hne : (insert x A).card ≠ Fintype.card S :=
      fun hc => h (Finset.eq_univ_of_card (insert x A) hc)
    omega

private def setVec {S : Type} [Fintype S] [DecidableEq S] : {k : ℕ} → (Fin k → S) → Finset S
  | 0, _ => ∅
  | _ + 1, w => stepSet (setVec (fun i => w i.castSucc)) (w (Fin.last _))

private def hitsVec {S : Type} [Fintype S] [DecidableEq S] : {k : ℕ} → (Fin k → S) → ℝ
  | 0, _ => 0
  | _ + 1, w =>
    hitsVec (fun i => w i.castSucc) +
      stepHit (setVec (fun i => w i.castSucc)) (w (Fin.last _))

private lemma card_setVec_lt {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    {k : ℕ} (v : Fin k → S) :
    (setVec v).card < Fintype.card S := by
  induction k with
  | zero =>
    unfold setVec
    simp [Fintype.card_pos]
  | succ k _ =>
    unfold setVec
    exact card_stepSet_lt _ _

private lemma setVec_snocFun {S : Type} [Fintype S] [DecidableEq S] {k : ℕ} (v : Fin k → S) (x : S) :
    setVec (snocFun v x) = stepSet (setVec v) x := by
  conv_lhs => unfold setVec
  have h1 : (fun i : Fin k => snocFun v x i.castSucc) = v := by
    ext i
    simp [snocFun, i.isLt]
  have h2 : snocFun v x (Fin.last k) = x := by
    simp [snocFun, Fin.last]
  rw [h1, h2]

private lemma hitsVec_snocFun {S : Type} [Fintype S] [DecidableEq S] {k : ℕ} (v : Fin k → S) (x : S) :
    hitsVec (snocFun v x) = hitsVec v + stepHit (setVec v) x := by
  conv_lhs => unfold hitsVec
  have h1 : (fun i : Fin k => snocFun v x i.castSucc) = v := by
    ext i
    simp [snocFun, i.isLt]
  have h2 : snocFun v x (Fin.last k) = x := by
    simp [snocFun, Fin.last]
  rw [h1, h2]

private noncomputable def psi (n r : ℕ) : ℝ :=
  ∑ m ∈ Finset.range r, (n : ℝ) / ((n : ℝ) - (m : ℝ))

private lemma psi_nonneg (n r : ℕ) (hr : r ≤ n) : 0 ≤ psi n r := by
  unfold psi
  refine Finset.sum_nonneg fun m hm => ?_
  have hm_lt : m < n := lt_of_lt_of_le (Finset.mem_range.mp hm) hr
  have hm_real : (m : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hm_lt
  exact div_nonneg (Nat.cast_nonneg n) (by linarith)

private lemma step_potential_eq {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (A : Finset S) (hA : A.card < Fintype.card S) (x : S) :
    ((Fintype.card S : ℝ) * (harmonic (Fintype.card S) : ℝ)) * stepHit A x +
        psi (Fintype.card S) (stepSet A x).card - psi (Fintype.card S) A.card =
      if x ∉ A then (Fintype.card S : ℝ) / ((Fintype.card S : ℝ) - (A.card : ℝ)) else 0 := by
  let n : ℕ := Fintype.card S
  change ((n : ℝ) * (harmonic n : ℝ)) * stepHit A x +
      psi n (stepSet A x).card - psi n A.card =
    if x ∉ A then (n : ℝ) / ((n : ℝ) - (A.card : ℝ)) else 0
  by_cases hx : x ∈ A
  · have hnot : ¬ (x ∉ A) := not_not.mpr hx
    rw [if_neg hnot]
    have hins : insert x A = A := Finset.insert_eq_of_mem hx
    have hne : insert x A ≠ Finset.univ := by
      rw [hins]
      intro heq
      have hc : A.card = n := by dsimp [n]; rw [heq, Finset.card_univ]
      omega
    unfold stepHit stepSet
    rw [if_neg hne, if_neg hne, hins]
    ring
  · rw [if_pos hx]
    have hcard_ins : (insert x A).card = A.card + 1 := Finset.card_insert_of_notMem hx
    by_cases hfull : A.card + 1 = n
    · have huniv : insert x A = Finset.univ :=
        Finset.eq_univ_of_card (insert x A) (by dsimp [n] at hfull; omega)
      unfold stepHit stepSet
      rw [if_pos huniv, if_pos huniv]
      have hpsi0 : psi n (∅ : Finset S).card = 0 := by simp [psi]
      have hpsi_n : psi n n = (n : ℝ) * (harmonic n : ℝ) := sum_div_sub_eq_mul_harmonic n
      have hpsi_succ : psi n (A.card + 1) =
          psi n A.card + (n : ℝ) / ((n : ℝ) - (A.card : ℝ)) :=
        Finset.sum_range_succ (fun m => (n : ℝ) / ((n : ℝ) - (m : ℝ))) A.card
      rw [hfull, hpsi_n] at hpsi_succ
      have hsub : (n : ℝ) - (A.card : ℝ) = 1 := by
        have h1 : ((A.card + 1 : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast hfull
        push_cast at h1
        linarith
      rw [hpsi0]
      linarith
    · have hne : insert x A ≠ Finset.univ := by
        intro heq
        have hc : (insert x A).card = n := by dsimp [n]; rw [heq, Finset.card_univ]
        omega
      unfold stepHit stepSet
      rw [if_neg hne, if_neg hne, hcard_ins]
      have hpsi_succ : psi n (A.card + 1) =
          psi n A.card + (n : ℝ) / ((n : ℝ) - (A.card : ℝ)) :=
        Finset.sum_range_succ (fun m => (n : ℝ) / ((n : ℝ) - (m : ℝ))) A.card
      linarith

private lemma sum_step_potential {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (A : Finset S) (hA : A.card < Fintype.card S) :
    ∑ x : S,
      (((Fintype.card S : ℝ) * (harmonic (Fintype.card S) : ℝ)) * stepHit A x +
        psi (Fintype.card S) (stepSet A x).card - psi (Fintype.card S) A.card) =
      (Fintype.card S : ℝ) := by
  simp_rw [step_potential_eq A hA]
  have h1 : ∀ x : S,
      (if x ∉ A then (Fintype.card S : ℝ) / ((Fintype.card S : ℝ) - (A.card : ℝ)) else 0) =
        ((Fintype.card S : ℝ) / ((Fintype.card S : ℝ) - (A.card : ℝ))) *
          (if x ∉ A then (1 : ℝ) else 0) := by
    intro x
    split_ifs <;> ring
  simp_rw [h1, ← Finset.mul_sum, sum_notMem_finset]
  have hr_lt : (A.card : ℝ) < (Fintype.card S : ℝ) := Nat.cast_lt.mpr hA
  have hdiff_ne : (Fintype.card S : ℝ) - (A.card : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr hr_lt)
  exact div_mul_cancel₀ (Fintype.card S : ℝ) hdiff_ne

private lemma sum_potential_hitsVec {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] (k : ℕ) :
    ∑ v : (Fin k → S),
      (((Fintype.card S : ℝ) * (harmonic (Fintype.card S) : ℝ)) * hitsVec v +
        psi (Fintype.card S) (setVec v).card) =
      (k : ℝ) * ((Fintype.card S : ℝ) ^ k) := by
  let n : ℝ := (Fintype.card S : ℝ)
  let H : ℝ := (harmonic (Fintype.card S) : ℝ)
  let N : ℕ := Fintype.card S
  change ∑ v : (Fin k → S), ((n * H) * hitsVec v + psi N (setVec v).card) = (k : ℝ) * (n ^ k)
  induction k with
  | zero =>
    unfold hitsVec setVec psi
    simp
  | succ k ih =>
    rw [← Equiv.sum_comp (snocEquiv k)
        (fun w => (n * H) * hitsVec w + psi N (setVec w).card),
        Fintype.sum_prod_type]
    change ∑ v : (Fin k → S), ∑ x : S,
        ((n * H) * hitsVec (snocFun v x) + psi N (setVec (snocFun v x)).card) =
      ((k + 1 : ℕ) : ℝ) * (n ^ (k + 1))
    simp_rw [hitsVec_snocFun, setVec_snocFun]
    have hinner : ∀ v : (Fin k → S),
        (∑ x : S, ((n * H) * (hitsVec v + stepHit (setVec v) x) +
            psi N (stepSet (setVec v) x).card)) =
          n * ((n * H) * hitsVec v + psi N (setVec v).card) + n := by
      intro v
      have hsplit : ∀ x : S,
          (n * H) * (hitsVec v + stepHit (setVec v) x) + psi N (stepSet (setVec v) x).card =
            ((n * H) * hitsVec v + psi N (setVec v).card) +
              ((n * H) * stepHit (setVec v) x + psi N (stepSet (setVec v) x).card -
                psi N (setVec v).card) := by
        intro x; ring
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib]
      have hconst : (∑ _x : S, ((n * H) * hitsVec v + psi N (setVec v).card)) =
          n * ((n * H) * hitsVec v + psi N (setVec v).card) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [hconst, sum_step_potential (setVec v) (card_setVec_lt v)]
    simp_rw [hinner]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ih]
    have hcard_v : (∑ _v : (Fin k → S), n) = (n ^ k) * n := by
      simp [n, Finset.sum_const, Finset.card_univ]
    rw [hcard_v, pow_succ]
    push_cast
    ring

private def phaseSet {S : Type} [Fintype S] [DecidableEq S] {j : ℕ} (v : Fin j → S) :
    ℕ → Finset S
  | 0 => ∅
  | k + 1 => if hk : k < j then stepSet (phaseSet v k) (v ⟨k, hk⟩) else phaseSet v k

private lemma phaseSet_succ {S : Type} [Fintype S] [DecidableEq S] {j : ℕ}
    (v : Fin j → S) (k : Fin j) :
    phaseSet v (k.val + 1) = stepSet (phaseSet v k.val) (v k) := by
  conv_lhs => unfold phaseSet
  rw [dif_pos k.isLt]

private lemma phaseSet_eq_setVec {S : Type} [Fintype S] [DecidableEq S] {j : ℕ} (v : Fin j → S)
    (k : ℕ) (hk : k ≤ j) :
    phaseSet v k = setVec (fun i : Fin k => v ⟨i.val, lt_of_lt_of_le i.isLt hk⟩) := by
  induction k with
  | zero =>
    unfold phaseSet setVec
    rfl
  | succ k ih =>
    have hk_lt : k < j := hk
    rw [phaseSet_succ v ⟨k, hk_lt⟩, ih (le_of_lt hk_lt)]
    rfl

private lemma sum_stepHit_eq_hitsVec {S : Type} [Fintype S] [DecidableEq S] {j : ℕ} (v : Fin j → S)
    (k : ℕ) (hk : k ≤ j) :
    (∑ i : Fin k,
        stepHit (phaseSet v i.val) (v ⟨i.val, lt_of_lt_of_le i.isLt hk⟩)) =
      hitsVec (fun i : Fin k => v ⟨i.val, lt_of_lt_of_le i.isLt hk⟩) := by
  induction k with
  | zero =>
    unfold hitsVec
    simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih (le_of_lt hk)]
    conv_rhs => unfold hitsVec
    congr 1
    rw [phaseSet_eq_setVec v k (le_of_lt hk)]
    rfl

private lemma card_phaseSet_lt {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {j : ℕ}
    (v : Fin j → S) (k : ℕ) :
    (phaseSet v k).card < Fintype.card S := by
  induction k with
  | zero =>
    unfold phaseSet
    simp [Fintype.card_pos]
  | succ k ih =>
    unfold phaseSet
    split_ifs with hk
    · exact card_stepSet_lt _ _
    · exact ih

private noncomputable def pickNotMem {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (A : Finset S) (hA : A.card < Fintype.card S) : S :=
  Classical.choose (by
    by_contra hall
    push Not at hall
    have heq : A = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    have hc : A.card = Fintype.card S := by rw [heq, Finset.card_univ]
    omega : ∃ s : S, s ∉ A)

private lemma pickNotMem_spec {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (A : Finset S) (hA : A.card < Fintype.card S) :
    pickNotMem A hA ∉ A :=
  Classical.choose_spec (by
    by_contra hall
    push Not at hall
    have heq : A = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    have hc : A.card = Fintype.card S := by rw [heq, Finset.card_univ]
    omega : ∃ s : S, s ∉ A)

private noncomputable def targetFromEnd {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {j : ℕ}
    (v : Fin j → S) : ℕ → S
  | 0 => pickNotMem (phaseSet v j) (card_phaseSet_lt v j)
  | m + 1 =>
    if hm : j - (m + 1) < j then
      let k : Fin j := ⟨j - (m + 1), hm⟩
      if insert (v k) (phaseSet v k.val) = Finset.univ then v k
      else targetFromEnd v m
    else pickNotMem (phaseSet v j) (card_phaseSet_lt v j)

private noncomputable def targetAt {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {j : ℕ}
    (v : Fin j → S) (k : ℕ) : S :=
  targetFromEnd v (j - k)

private lemma targetAt_fin {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {j : ℕ}
    (v : Fin j → S) (k : Fin j) :
    targetAt v k.val =
      if insert (v k) (phaseSet v k.val) = Finset.univ then v k
      else targetAt v (k.val + 1) := by
  unfold targetAt
  have hsub : j - k.val = (j - (k.val + 1)) + 1 := by omega
  have hidx : j - ((j - (k.val + 1)) + 1) = k.val := by omega
  have hlt : j - ((j - (k.val + 1)) + 1) < j := by omega
  rw [hsub]
  dsimp [targetFromEnd]
  rw [dif_pos hlt]
  have hfin : (⟨j - (j - (k.val + 1) + 1), hlt⟩ : Fin j) = k := Fin.ext hidx
  simp only [hfin]
  rw [hidx]

private lemma targetAt_fin_pos {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {j : ℕ}
    (v : Fin j → S) (k : Fin j) (h : insert (v k) (phaseSet v k.val) = Finset.univ) :
    targetAt v k.val = v k := by
  rw [targetAt_fin v k, if_pos h]

private lemma targetAt_fin_neg {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {j : ℕ}
    (v : Fin j → S) (k : Fin j) (h : insert (v k) (phaseSet v k.val) ≠ Finset.univ) :
    targetAt v k.val = targetAt v (k.val + 1) := by
  rw [targetAt_fin v k, if_neg h]

private lemma targetAt_notMem {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {j : ℕ}
    (v : Fin j → S) (m : ℕ) (hm : m ≤ j) :
    targetAt v (j - m) ∉ phaseSet v (j - m) := by
  induction m with
  | zero =>
    have hj : j - 0 = j := Nat.sub_zero j
    rw [hj]
    unfold targetAt
    simp only [Nat.sub_self, targetFromEnd]
    exact pickNotMem_spec (phaseSet v j) (card_phaseSet_lt v j)
  | succ m ih =>
    let k : Fin j := ⟨j - (m + 1), by omega⟩
    have hk_val : j - (m + 1) = k.val := rfl
    have hk_succ : k.val + 1 = j - m := by dsimp [k]; omega
    rw [hk_val, targetAt_fin v k]
    split_ifs with huniv
    · intro hmem
      have hins : insert (v k) (phaseSet v k.val) = phaseSet v k.val :=
        Finset.insert_eq_of_mem hmem
      rw [hins] at huniv
      have hc : (phaseSet v k.val).card = Fintype.card S := by
        rw [huniv, Finset.card_univ]
      have hlt := card_phaseSet_lt v k.val
      omega
    · rw [hk_succ]
      have hstep : phaseSet v (j - m) = insert (v k) (phaseSet v k.val) := by
        rw [← hk_succ, phaseSet_succ v k, stepSet_neg huniv]
      have hnot_ins : targetAt v (j - m) ∉ insert (v k) (phaseSet v k.val) := by
        rw [← hstep]
        exact ih (by omega)
      exact fun hmem => hnot_ins (Finset.mem_insert_of_mem hmem)

private lemma targetAt_succ_notMem {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {j : ℕ}
    (v : Fin j → S) (k : Fin j) :
    targetAt v (k.val + 1) ∉ phaseSet v (k.val + 1) := by
  have h := targetAt_notMem v (j - (k.val + 1)) (by omega)
  have heq : j - (j - (k.val + 1)) = k.val + 1 := by omega
  rwa [heq] at h

private noncomputable def phaseSched {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) {j : ℕ} (v : Fin j → S) (i : Fin (j + 1)) : S :=
  if i.val = 0 then s₀ else targetAt v i.val

open Classical in
private lemma offlineOpt_le_hitsVec_add_one {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (s₀ : S) {j : ℕ} (v : Fin j → S) :
    offlineOpt (uniformD (S := S)) s₀ (fun i : Fin j => unitTask (v i)) ≤
      hitsVec v + 1 := by
  have hmem : phaseSched s₀ v ∈
      Finset.univ.filter (fun σ : Fin (j + 1) → S => σ 0 = s₀) := by
    simp [phaseSched]
  have hinf := Finset.inf'_le
    (f := fun σ => schedCost (uniformD (S := S)) (fun i => unitTask (v i)) σ) hmem
  refine le_trans hinf ?_
  unfold schedCost
  have hstep : ∀ k : Fin j,
      uniformD (phaseSched s₀ v k.castSucc) (phaseSched s₀ v k.succ) +
          unitTask (v k) (phaseSched s₀ v k.succ) ≤
        stepHit (phaseSet v k.val) (v k) + (if k.val = 0 then (1 : ℝ) else 0) := by
    intro k
    have hsucc : phaseSched s₀ v k.succ = targetAt v (k.val + 1) := rfl
    rw [hsucc]
    by_cases huniv : insert (v k) (phaseSet v k.val) = Finset.univ
    · rw [stepHit_pos huniv]
      by_cases hk0 : k.val = 0
      · rw [if_pos hk0]
        dsimp [uniformD, unitTask]
        split_ifs <;> norm_num
      · rw [if_neg hk0]
        have hcast : phaseSched s₀ v k.castSucc = v k := by
          dsimp [phaseSched]
          rw [if_neg hk0, targetAt_fin_pos v k huniv]
        rw [hcast]
        dsimp [uniformD, unitTask]
        by_cases h1 : v k = targetAt v (k.val + 1)
        · rw [if_pos h1, if_pos h1.symm]; norm_num
        · have h2 : targetAt v (k.val + 1) ≠ v k := Ne.symm h1
          rw [if_neg h1, if_neg h2]
    · rw [stepHit_neg huniv]
      have hphase_succ : phaseSet v (k.val + 1) = insert (v k) (phaseSet v k.val) := by
        rw [phaseSet_succ v k, stepSet_neg huniv]
      have hnot_mem : targetAt v (k.val + 1) ∉ insert (v k) (phaseSet v k.val) := by
        rw [← hphase_succ]
        exact targetAt_succ_notMem v k
      have hne_vk : targetAt v (k.val + 1) ≠ v k := by
        intro heq
        apply hnot_mem
        rw [heq]
        exact Finset.mem_insert_self (v k) _
      have hunit : unitTask (v k) (targetAt v (k.val + 1)) = 0 := by
        dsimp [unitTask]
        exact if_neg hne_vk
      rw [hunit, add_zero]
      by_cases hk0 : k.val = 0
      · rw [if_pos hk0]
        dsimp [uniformD]
        split_ifs <;> norm_num
      · rw [if_neg hk0]
        have hcast : phaseSched s₀ v k.castSucc = targetAt v (k.val + 1) := by
          dsimp [phaseSched]
          rw [if_neg hk0, targetAt_fin_neg v k huniv]
        rw [hcast]
        dsimp [uniformD]
        rw [if_pos rfl]
        norm_num
  calc ∑ k : Fin j,
        (uniformD (phaseSched s₀ v k.castSucc) (phaseSched s₀ v k.succ) +
          unitTask (v k) (phaseSched s₀ v k.succ))
      ≤ ∑ k : Fin j, (stepHit (phaseSet v k.val) (v k) + (if k.val = 0 then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum fun k _ => hstep k
    _ = (∑ k : Fin j, stepHit (phaseSet v k.val) (v k)) +
          ∑ k : Fin j, (if k.val = 0 then (1 : ℝ) else 0) :=
        Finset.sum_add_distrib
    _ ≤ hitsVec v + 1 := by
        have h1 := sum_stepHit_eq_hitsVec v j (le_refl j)
        have hv_eq : (fun i : Fin j => v ⟨i.val, lt_of_lt_of_le i.isLt (le_refl j)⟩) = v := by
          ext i; rfl
        rw [hv_eq] at h1
        rw [h1]
        have h2 : (∑ k : Fin j, (if k.val = 0 then (1 : ℝ) else 0)) ≤ 1 := by
          cases j with
          | zero => simp
          | succ j' =>
            have hcongr : ∀ k : Fin (j' + 1),
                (if k.val = 0 then (1 : ℝ) else 0) = if k = 0 then 1 else 0 := by
              intro k
              by_cases hk : k = 0
              · subst hk; simp
              · have hk_val : k.val ≠ 0 := fun h => hk (Fin.ext h)
                simp [hk, hk_val]
            simp_rw [hcongr]
            simp
        linarith

theorem solution {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [MeasurableSpace S] [MeasurableSingletonClass S] (s₀ : S) :
    ∃ C : ℝ, ∀ j : ℕ,
      expOfflineCost (uniformD (S := S)) s₀ (unitTask (S := S)) (uniformStateSeq S) j ≤
        (j : ℝ) / ((Fintype.card S : ℝ) * (harmonic (Fintype.card S) : ℝ)) + C := by
  refine ⟨1, fun j => ?_⟩
  let n : ℝ := (Fintype.card S : ℝ)
  let H : ℝ := (harmonic (Fintype.card S) : ℝ)
  have hn_pos : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hnH_pos : 0 < n * H := by
    rw [← sum_div_sub_eq_mul_harmonic (Fintype.card S)]
    have h0_mem : 0 ∈ Finset.range (Fintype.card S) := Finset.mem_range.mpr Fintype.card_pos
    have h0_pos : (0 : ℝ) < (fun r : ℕ => n / (n - (r : ℝ))) 0 := by
      dsimp
      simp only [Nat.cast_zero, sub_zero, div_self (ne_of_gt hn_pos), zero_lt_one]
    refine lt_of_lt_of_le h0_pos
      (Finset.single_le_sum (f := fun r : ℕ => n / (n - (r : ℝ))) (fun r hr => ?_) h0_mem)
    have hr_lt : (r : ℝ) < n := Nat.cast_lt.mpr (Finset.mem_range.mp hr)
    exact div_nonneg (le_of_lt hn_pos) (by linarith)
  unfold expOfflineCost
  have hprefix : ∀ ω : ℕ → S,
      offlineOpt (uniformD (S := S)) s₀ (prefixTasks (unitTask (S := S)) ω j) =
        offlineOpt (uniformD (S := S)) s₀ (fun i : Fin j => unitTask (ω i)) :=
    fun _ => rfl
  simp_rw [hprefix]
  rw [integral_uniformStateSeq_fin j
      (fun v : Fin j → S => offlineOpt (uniformD (S := S)) s₀ (fun i => unitTask (v i)))]
  have hsum_off : (∑ v : (Fin j → S),
      offlineOpt (uniformD (S := S)) s₀ (fun i => unitTask (v i))) ≤
        (∑ v : (Fin j → S), hitsVec v) + (n ^ j) := by
    calc (∑ v : (Fin j → S), offlineOpt (uniformD (S := S)) s₀ (fun i => unitTask (v i)))
        ≤ ∑ v : (Fin j → S), (hitsVec v + 1) :=
          Finset.sum_le_sum fun v _ => offlineOpt_le_hitsVec_add_one s₀ v
      _ = (∑ v : (Fin j → S), hitsVec v) + ∑ _v : (Fin j → S), (1 : ℝ) :=
          Finset.sum_add_distrib
      _ = (∑ v : (Fin j → S), hitsVec v) + (n ^ j) := by
          simp [n, Finset.sum_const, Finset.card_univ]
  have hsum_hits : (n * H) * (∑ v : (Fin j → S), hitsVec v) ≤ (j : ℝ) * (n ^ j) := by
    rw [Finset.mul_sum, ← sum_potential_hitsVec (S := S) j]
    refine Finset.sum_le_sum fun v _ => ?_
    have hpsi := psi_nonneg (Fintype.card S) (setVec v).card (le_of_lt (card_setVec_lt v))
    linarith
  have hhits_div : (n⁻¹ ^ j) * (∑ v : (Fin j → S), hitsVec v) ≤ (j : ℝ) / (n * H) := by
    rw [le_div_iff₀ hnH_pos]
    calc ((n⁻¹ ^ j) * ∑ v : (Fin j → S), hitsVec v) * (n * H)
        = (n⁻¹ ^ j) * ((n * H) * ∑ v : (Fin j → S), hitsVec v) := by ring
      _ ≤ (n⁻¹ ^ j) * ((j : ℝ) * (n ^ j)) :=
          mul_le_mul_of_nonneg_left hsum_hits (by positivity)
      _ = (j : ℝ) * ((n⁻¹ * n) ^ j) := by
          rw [mul_pow]; ring
      _ = (j : ℝ) := by
          rw [inv_mul_cancel₀ (ne_of_gt hn_pos), one_pow, mul_one]
  calc (n⁻¹ ^ j) * ∑ v : (Fin j → S),
        offlineOpt (uniformD (S := S)) s₀ (fun i => unitTask (v i))
      ≤ (n⁻¹ ^ j) * ((∑ v : (Fin j → S), hitsVec v) + (n ^ j)) :=
        mul_le_mul_of_nonneg_left hsum_off (by positivity)
    _ = (n⁻¹ ^ j) * (∑ v : (Fin j → S), hitsVec v) + (n⁻¹ * n) ^ j := by
        rw [mul_add, ← mul_pow]
    _ = (n⁻¹ ^ j) * (∑ v : (Fin j → S), hitsVec v) + 1 := by
        rw [inv_mul_cancel₀ (ne_of_gt hn_pos), one_pow]
    _ ≤ (j : ℝ) / (n * H) + 1 := by linarith
