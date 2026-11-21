-- Prove2me | solution 1 for MNLStability.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T23:16:24.816794+00:00
-- url     : https://prove2.me/submissions/b9d1151d-868d-450d-a066-818b8252d048

import Mathlib
import Definitions.Def_MNLStability_IsLaw
import Definitions.Def_MNLStability_expX
import Definitions.Def_MNLStability_opt
import Definitions.Def_MNLStability_swap
import Definitions.Def_MNLStability_IsSpaced
import Definitions.Def_MNLStability_scaleProd
import Definitions.Def_MNLStability_prob
import Definitions.Def_MNLStability_IsUpSetOff
import Definitions.Def_MNLStability_choiceRatio

open scoped ENNReal

namespace Aux_MNLS0
open MNLStability

variable {n : ℕ}

abbrev St (n : ℕ) := (Fin n → ℕ) × ℕ

noncomputable def EEx {α : Type*} (μ : PMF α) (f : α → ℝ≥0∞) : ℝ≥0∞ := ∑' x, μ x * f x

lemma EEx_pure {α : Type*} (a : α) (f : α → ℝ≥0∞) : EEx (PMF.pure a) f = f a := by
  unfold EEx
  rw [tsum_eq_single a]
  · simp [PMF.pure_apply]
  · intro b hb
    simp [PMF.pure_apply, hb]

lemma EEx_bind {α β : Type*} (μ : PMF α) (K : α → PMF β) (f : β → ℝ≥0∞) :
    EEx (μ.bind K) f = ∑' a, μ a * EEx (K a) f := by
  unfold EEx
  simp only [PMF.bind_apply]
  calc ∑' x, (∑' a, μ a * K a x) * f x = ∑' x, ∑' a, μ a * K a x * f x := by
        refine tsum_congr (fun x => ?_)
        rw [ENNReal.tsum_mul_right]
    _ = ∑' a, ∑' x, μ a * K a x * f x := ENNReal.tsum_comm
    _ = ∑' a, μ a * ∑' x, K a x * f x := by
        refine tsum_congr (fun a => ?_)
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr (fun x => ?_)
        ring

lemma EEx_map {α β : Type*} (μ : PMF α) (h : α → β) (f : β → ℝ≥0∞) :
    EEx (μ.map h) f = ∑' a, μ a * f (h a) := by
  rw [← PMF.bind_pure_comp, EEx_bind]
  refine tsum_congr (fun a => ?_)
  rw [Function.comp_apply, EEx_pure]

lemma EEx_le {α : Type*} (μ : PMF α) (f : α → ℝ≥0∞) (B : ℝ≥0∞) (h : ∀ x, f x ≤ B) :
    EEx μ f ≤ B := by
  unfold EEx
  calc ∑' x, μ x * f x ≤ ∑' x, μ x * B :=
        ENNReal.tsum_le_tsum (fun x => mul_le_mul_of_nonneg_left (h x) (zero_le))
    _ = B := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

lemma EEx_mono {α : Type*} (μ : PMF α) (f g : α → ℝ≥0∞) (h : ∀ x, f x ≤ g x) :
    EEx μ f ≤ EEx μ g :=
  ENNReal.tsum_le_tsum (fun x => mul_le_mul_of_nonneg_left (h x) (zero_le))

lemma EEx_congr {α : Type*} (μ : PMF α) (f g : α → ℝ≥0∞) (h : ∀ x, μ x ≠ 0 → f x = g x) :
    EEx μ f = EEx μ g := by
  unfold EEx
  refine tsum_congr (fun x => ?_)
  by_cases hx : μ x = 0
  · rw [hx, zero_mul, zero_mul]
  · rw [h x hx]

lemma EEx_const_mul {α : Type*} (μ : PMF α) (c : ℝ≥0∞) (f : α → ℝ≥0∞) :
    EEx μ (fun x => c * f x) = c * EEx μ f := by
  unfold EEx
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr (fun x => ?_)
  ring

lemma EEx_add {α : Type*} (μ : PMF α) (f g : α → ℝ≥0∞) :
    EEx μ (fun x => f x + g x) = EEx μ f + EEx μ g := by
  unfold EEx
  rw [← ENNReal.tsum_add]
  refine tsum_congr (fun x => ?_)
  ring

def shf : Option (Fin n) → St n → St n
  | none, x => (x.1, x.2 + 1)
  | some i, x => (x.1 + Pi.single i 1, x.2)

def sb1 (V : Fin n → ℕ) : Option (Fin n) → (Fin n → ℕ)
  | none => V
  | some i => V - Pi.single i 1

lemma demand_zero (wt : Weights n) (U : Fin n → ℕ) : demand wt U 0 = PMF.pure (0, 0) := by
  simp only [demand]

lemma demand_succ (wt : Weights n) (U : Fin n → ℕ) (m : ℕ) :
    demand wt U (m + 1) =
      (demand wt U m).bind (fun x => (step wt (U - x.1)).map (fun c => shf c x)) := by
  first
  | rfl
  | (simp only [demand]
     congr 1
     funext x
     congr 1
     funext c
     cases c <;> rfl)

lemma step_sum_one (wt : Weights n) (V : Fin n → ℕ) : ∑ c, step wt V c = 1 := by
  have := PMF.tsum_coe (step wt V)
  rwa [tsum_fintype] at this

lemma EEx_succ_fwd (wt : Weights n) (U : Fin n → ℕ) (m : ℕ) (f : St n → ℝ≥0∞) :
    EEx (demand wt U (m + 1)) f =
      EEx (demand wt U m) (fun x => ∑ c, step wt (U - x.1) c * f (shf c x)) := by
  rw [demand_succ, EEx_bind]
  simp only [EEx_map, tsum_fintype] <;> rfl

lemma shf_comm (c d : Option (Fin n)) (x : St n) : shf d (shf c x) = shf c (shf d x) := by
  rcases c with _ | i <;> rcases d with _ | j
  · rfl
  · rfl
  · rfl
  · refine Prod.ext ?_ rfl
    show x.1 + Pi.single i 1 + Pi.single j 1 = x.1 + Pi.single j 1 + Pi.single i 1
    abel

lemma sub_shf (V : Fin n → ℕ) (c : Option (Fin n)) (x : St n) :
    V - (shf c x).1 = sb1 V c - x.1 := by
  rcases c with _ | i
  · rfl
  · show V - (x.1 + Pi.single i 1) = V - Pi.single i 1 - x.1
    rw [tsub_tsub, add_comm]

lemma EEx_succ_bwd (wt : Weights n) (m : ℕ) : ∀ (V : Fin n → ℕ) (f : St n → ℝ≥0∞),
    EEx (demand wt V (m + 1)) f =
      ∑ c, step wt V c * EEx (demand wt (sb1 V c) m) (f ∘ shf c) := by
  induction m with
  | zero =>
    intro V f
    rw [EEx_succ_fwd, demand_zero, EEx_pure]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [demand_zero, EEx_pure, Function.comp_apply]
    simp only [tsub_zero]
  | succ m ih =>
    intro V f
    rw [EEx_succ_fwd, ih]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [EEx_succ_fwd]
    congr 2
    funext x
    simp only [Function.comp_apply]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [shf_comm c d x, sub_shf V c x]

noncomputable def qq (wt : Weights n) (V : Fin n → ℕ) : Option (Fin n) → ℝ
  | none => wt.w0
  | some i => if 0 < V i then wt.w i else 0

lemma qq_nonneg (wt : Weights n) (hw : wt.Pos) (V : Fin n → ℕ) (c : Option (Fin n)) :
    0 ≤ qq wt V c := by
  rcases c with _ | i
  · exact hw.1.le
  · simp only [qq]
    split_ifs <;> linarith [hw.2 i]

lemma ZZ_eq (wt : Weights n) (V : Fin n → ℕ) :
    ∑ c, qq wt V c = wt.w0 + wt.wsum (inStock V) := by
  rw [Fintype.sum_option]
  simp only [qq, Weights.wsum, inStock, Finset.sum_filter]

lemma Z_pos (wt : Weights n) (hw : wt.Pos) (V : Fin n → ℕ) : 0 < ∑ d, qq wt V d := by
  rw [ZZ_eq]
  have : 0 ≤ wt.wsum (inStock V) := Finset.sum_nonneg (fun i _ => (hw.2 i).le)
  linarith [hw.1]

lemma stepMass_eq (wt : Weights n) (V : Fin n → ℕ) (c : Option (Fin n)) :
    stepMass wt V c = ENNReal.ofReal (qq wt V c / ∑ d, qq wt V d) := by
  rw [ZZ_eq]
  rcases c with _ | i
  · rfl
  · simp only [stepMass, qq]
    split_ifs <;> simp

lemma step_eq (wt : Weights n) (hw : wt.Pos) (V : Fin n → ℕ) (c : Option (Fin n)) :
    step wt V c = ENNReal.ofReal (qq wt V c / ∑ d, qq wt V d) := by
  have hZ : 0 < ∑ d, qq wt V d := Z_pos wt hw V
  have hsum : ∑ a, stepMass wt V a = 1 := by
    simp only [stepMass_eq]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun d _ => div_nonneg (qq_nonneg wt hw V d) hZ.le),
      ← Finset.sum_div, div_self hZ.ne', ENNReal.ofReal_one]
  unfold step
  rw [dif_pos hsum, PMF.ofFintype_apply, stepMass_eq]

lemma avail_of_ne (wt : Weights n) (hw : wt.Pos) (V : Fin n → ℕ) (i : Fin n)
    (h : step wt V (some i) ≠ 0) : 0 < V i := by
  by_contra hc
  apply h
  rw [step_eq wt hw]
  simp only [qq, if_neg hc, zero_div, ENNReal.ofReal_zero]

lemma sum_le_avail (wt : Weights n) (hw : wt.Pos) (V : Fin n → ℕ)
    (A B : Option (Fin n) → ℝ≥0∞) (h : ∀ c, (∀ i, c = some i → 0 < V i) → A c ≤ B c) :
    ∑ c, step wt V c * A c ≤ ∑ c, step wt V c * B c := by
  refine Finset.sum_le_sum (fun c _ => ?_)
  by_cases hc : step wt V c = 0
  · rw [hc, zero_mul, zero_mul]
  · refine mul_le_mul_of_nonneg_left (h c ?_) (zero_le)
    rintro i rfl
    exact avail_of_ne wt hw V i hc

lemma sum_ofReal_mul {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ c, 0 ≤ a c)
    (G : ι → ℝ≥0∞) (hG : ∀ c, G c ≠ ⊤) :
    ∑ c, ENNReal.ofReal (a c) * G c = ENNReal.ofReal (∑ c, a c * (G c).toReal) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun c _ => mul_nonneg (ha c) ENNReal.toReal_nonneg)]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [ENNReal.ofReal_mul (ha c), ENNReal.ofReal_toReal (hG c)]

lemma key_alg {ι : Type*} [Fintype ι] [DecidableEq ι] (o : ι) (q q' : ι → ℝ)
    (hq : ∀ c, 0 ≤ q c) (hZ : 0 < ∑ c, q c) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hq' : ∀ c, q' c = if c = o then (1 - ε) * q c else q c)
    (G : ι → ℝ≥0∞) (hG : ∀ c, G c ≠ ⊤)
    (hkey : q o = 0 ∨ G o ≤ ∑ c, ENNReal.ofReal (q c / ∑ d, q d) * G c) :
    ∑ c, ENNReal.ofReal (q c / ∑ d, q d) * G c ≤
      ∑ c, ENNReal.ofReal (q' c / ∑ d, q' d) * G c := by
  have split : ∀ x : ι → ℝ, ∑ c, q' c * x c = ∑ c, q c * x c - ε * q o * x o := by
    intro x
    have h1 : ∀ c, q' c * x c = q c * x c - (if c = o then ε * q o * x o else 0) := by
      intro c
      rw [hq' c]
      split_ifs with h
      · subst h; ring
      · ring
    rw [Finset.sum_congr rfl (fun c _ => h1 c), Finset.sum_sub_distrib, Finset.sum_ite_eq',
      if_pos (Finset.mem_univ _)]
  have hq'0 : ∀ c, 0 ≤ q' c := by
    intro c
    rw [hq' c]
    split_ifs
    · exact mul_nonneg (by linarith) (hq c)
    · exact hq c
  have hZ' : ∑ c, q' c = ∑ c, q c - ε * q o := by
    have := split (fun _ => 1)
    simp only [mul_one] at this
    exact this
  have hqo : q o ≤ ∑ c, q c := Finset.single_le_sum (fun c _ => hq c) (Finset.mem_univ o)
  have hZ'pos : 0 < ∑ c, q c - ε * q o := by
    nlinarith [mul_nonneg hε0 (sub_nonneg.2 hqo), mul_pos (sub_pos.2 hε1) hZ]
  have hZ'pos' : 0 < ∑ c, q' c := by rw [hZ']; exact hZ'pos
  rw [sum_ofReal_mul _ (fun c => div_nonneg (hq c) hZ.le) G hG,
    sum_ofReal_mul _ (fun c => div_nonneg (hq'0 c) hZ'pos'.le) G hG]
  rw [sum_ofReal_mul _ (fun c => div_nonneg (hq c) hZ.le) G hG] at hkey
  apply ENNReal.ofReal_le_ofReal
  have e1 : ∑ c, q c / (∑ d, q d) * (G c).toReal = (∑ c, q c * (G c).toReal) / ∑ d, q d := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    ring
  have e2 : ∑ c, q' c / (∑ d, q' d) * (G c).toReal =
      (∑ c, q' c * (G c).toReal) / ∑ d, q' d := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    ring
  rw [e1, e2, split (fun c => (G c).toReal), hZ', div_le_div_iff₀ hZ hZ'pos]
  rcases hkey with h0 | h
  · rw [h0]; nlinarith
  · have h' : (G o).toReal ≤ (∑ c, q c * (G c).toReal) / ∑ d, q d := by
      rw [← e1]
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      rwa [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun c _ =>
        mul_nonneg (div_nonneg (hq c) hZ.le) ENNReal.toReal_nonneg))] at this
    rw [le_div_iff₀ hZ] at h'
    nlinarith [mul_nonneg (mul_nonneg hε0 (hq o)) (sub_nonneg.2 h')]

lemma key_alg2 {ι : Type*} [Fintype ι] [DecidableEq ι] (o : ι) (q q' : ι → ℝ)
    (hq : ∀ c, 0 ≤ q c) (hq' : ∀ c, q' c = if c = o then 0 else q c)
    (hZ' : 0 < ∑ c, q' c) (L R : ι → ℝ≥0∞) (hL : ∀ c, L c ≠ ⊤) (hR : ∀ c, R c ≠ ⊤)
    (hLR : ∀ c, c ≠ o → q c ≠ 0 → L c ≤ R c)
    (hRo : R o = ∑ c, ENNReal.ofReal (q' c / ∑ d, q' d) * L c) :
    ∑ c, ENNReal.ofReal (q' c / ∑ d, q' d) * L c ≤
      ∑ c, ENNReal.ofReal (q c / ∑ d, q d) * R c := by
  have split : ∀ x : ι → ℝ, ∑ c, q c * x c = ∑ c, q' c * x c + q o * x o := by
    intro x
    have h1 : ∀ c, q c * x c = q' c * x c + (if c = o then q o * x o else 0) := by
      intro c
      rw [hq' c]
      split_ifs with h
      · subst h; ring
      · ring
    rw [Finset.sum_congr rfl (fun c _ => h1 c), Finset.sum_add_distrib, Finset.sum_ite_eq',
      if_pos (Finset.mem_univ _)]
  have hq'0 : ∀ c, 0 ≤ q' c := by
    intro c
    rw [hq' c]
    split_ifs
    · exact le_rfl
    · exact hq c
  have hZsplit : ∑ c, q c = ∑ c, q' c + q o := by
    have := split (fun _ => 1)
    simp only [mul_one] at this
    exact this
  have hZ : 0 < ∑ c, q c := by rw [hZsplit]; linarith [hq o]
  rw [sum_ofReal_mul _ (fun c => div_nonneg (hq'0 c) hZ'.le) L hL,
    sum_ofReal_mul _ (fun c => div_nonneg (hq c) hZ.le) R hR]
  rw [sum_ofReal_mul _ (fun c => div_nonneg (hq'0 c) hZ'.le) L hL] at hRo
  apply ENNReal.ofReal_le_ofReal
  have e1 : ∑ c, q' c / (∑ d, q' d) * (L c).toReal = (∑ c, q' c * (L c).toReal) / ∑ d, q' d := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    ring
  have e2 : ∑ c, q c / (∑ d, q d) * (R c).toReal = (∑ c, q c * (R c).toReal) / ∑ d, q d := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    ring
  have hro : (R o).toReal * ∑ d, q' d = ∑ c, q' c * (L c).toReal := by
    rw [hRo, ENNReal.toReal_ofReal (Finset.sum_nonneg (fun c _ =>
      mul_nonneg (div_nonneg (hq'0 c) hZ'.le) ENNReal.toReal_nonneg)), e1,
      div_mul_cancel₀ _ hZ'.ne']
  have hge : ∑ c, q' c * (L c).toReal ≤ ∑ c, q' c * (R c).toReal := by
    refine Finset.sum_le_sum (fun c _ => ?_)
    by_cases hco : c = o
    · rw [hq' c, if_pos hco, zero_mul, zero_mul]
    · by_cases hqc : q c = 0
      · rw [hq' c, if_neg hco, hqc, zero_mul, zero_mul]
      · exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (hR c) (hLR c hco hqc)) (hq'0 c)
  rw [e1, e2, div_le_div_iff₀ hZ' hZ]
  calc (∑ c, q' c * (L c).toReal) * ∑ d, q d
      = (∑ c, q' c * (L c).toReal) * ∑ d, q' d + q o * ((R o).toReal * ∑ d, q' d) := by
        rw [hZsplit, hro]; ring
    _ ≤ (∑ c, q' c * (R c).toReal) * ∑ d, q' d + q o * ((R o).toReal * ∑ d, q' d) := by
        have := mul_le_mul_of_nonneg_right hge hZ'.le
        linarith
    _ =(∑ c, q c * (R c).toReal) * ∑ d, q' d := by
        rw [split (fun c => (R c).toReal)]; ring

def OffA (a : Fin n) (g : St n → ℝ≥0∞) : Prop :=
  ∀ x y : St n, (∀ j, j ≠ a → x.1 j = y.1 j) → x.2 = y.2 → g x = g y

def Adm (a : Fin n) (g : St n → ℝ≥0∞) : Prop :=
  Monotone g ∧ OffA a g ∧ ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ x, g x ≤ B

lemma shf_mono (c : Option (Fin n)) : Monotone (shf (n := n) c) := by
  intro x y hxy
  rw [Prod.le_def] at hxy ⊢
  rcases c with _ | i
  · show x.1 ≤ y.1 ∧ x.2 + 1 ≤ y.2 + 1
    exact ⟨hxy.1, Nat.add_le_add_right hxy.2 1⟩
  · show x.1 + Pi.single i 1 ≤ y.1 + Pi.single i 1 ∧ x.2 ≤ y.2
    exact ⟨add_le_add hxy.1 le_rfl, hxy.2⟩

lemma le_shf (c : Option (Fin n)) (x : St n) : x ≤ shf c x := by
  rw [Prod.le_def]
  rcases c with _ | i
  · exact ⟨le_rfl, Nat.le_succ _⟩
  · refine ⟨Pi.le_def.2 (fun j => ?_), le_rfl⟩
    show x.1 j ≤ x.1 j + (Pi.single i 1 : Fin n → ℕ) j
    exact Nat.le_add_right _ _

lemma Adm.comp {a : Fin n} {g : St n → ℝ≥0∞} (hg : Adm a g) (c : Option (Fin n)) :
    Adm a (g ∘ shf c) := by
  obtain ⟨h1, h2, B, hB, h3⟩ := hg
  refine ⟨h1.comp (shf_mono c), ?_, B, hB, fun x => h3 _⟩
  intro x y hxy h2'
  simp only [Function.comp_apply]
  apply h2
  · intro j hj
    rcases c with _ | i
    · exact hxy j hj
    · show x.1 j + (Pi.single i 1 : Fin n → ℕ) j = y.1 j + (Pi.single i 1 : Fin n → ℕ) j
      rw [hxy j hj]
  · rcases c with _ | i
    · show x.2 + 1 = y.2 + 1
      rw [h2']
    · exact h2'

lemma comp_shf_self {a : Fin n} {g : St n → ℝ≥0∞} (hg : OffA a g) : g ∘ shf (some a) = g := by
  funext x
  simp only [Function.comp_apply]
  refine hg _ _ (fun j hj => ?_) rfl
  show x.1 j + (Pi.single a 1 : Fin n → ℕ) j = x.1 j
  rw [Pi.single_eq_of_ne hj, add_zero]

noncomputable def fV (a : Fin n) (V : Fin n → ℕ) (r : ℕ) (g : St n → ℝ≥0∞) :
    St n → ℝ≥0∞ :=
  fun x => if r + x.1 a ≤ V a then g x else 0

lemma shf_fst (c : Option (Fin n)) (x : St n) (a : Fin n) :
    (shf c x).1 a = x.1 a + (if c = some a then 1 else 0) := by
  rcases c with _ | i
  · simp [shf]
  · by_cases h : i = a
    · subst h; simp [shf]
    · simp [shf, h, Pi.single_eq_of_ne' h]

lemma fV_shf (a : Fin n) (V : Fin n → ℕ) (r : ℕ) (g : St n → ℝ≥0∞) (c : Option (Fin n))
    (hc : ∀ i, c = some i → 0 < V i) :
    fV a V r g ∘ shf c = fV a (sb1 V c) r (g ∘ shf c) := by
  funext x
  simp only [Function.comp_apply, fV]
  rcases c with _ | i
  · rfl
  · have hi := hc i rfl
    rw [shf_fst]
    show (if r + (x.1 a + if some i = some a then 1 else 0) ≤ V a then g (shf (some i) x) else 0)
      = if r + x.1 a ≤ (V - (Pi.single i 1 : Fin n → ℕ)) a then g (shf (some i) x) else 0
    rw [Pi.sub_apply]
    by_cases hia : i = a
    · subst hia
      rw [if_pos rfl, Pi.single_eq_same]
      split_ifs <;> first | rfl | omega
    · have hne : ¬ (some i = some a) := fun h => hia (Option.some.inj h)
      rw [if_neg hne, Pi.single_eq_of_ne' hia, add_zero, tsub_zero]

lemma sb1_sub_comm (V : Fin n → ℕ) (a : Fin n) (c : Option (Fin n)) :
    sb1 (V - Pi.single a 1) c = sb1 V c - Pi.single a 1 := by
  rcases c with _ | i
  · rfl
  · show V - Pi.single a 1 - Pi.single i 1 = V - Pi.single i 1 - Pi.single a 1
    rw [tsub_right_comm]

lemma qq_congr (wt : Weights n) (V V' : Fin n → ℕ) (h : ∀ i, 0 < V i ↔ 0 < V' i) :
    qq wt V = qq wt V' := by
  funext c
  rcases c with _ | i
  · rfl
  · simp only [qq, h i]

theorem C_lem (wt : Weights n) (hw : wt.Pos) (a : Fin n) (r : ℕ) (m : ℕ) :
    ∀ (V : Fin n → ℕ) (g : St n → ℝ≥0∞), Adm a g →
    EEx (demand wt (V - Pi.single a 1) m) (fV a (V - Pi.single a 1) r g) ≤
      EEx (demand wt V (m + 1)) (fV a V r g) := by
  induction m with
  | zero =>
    intro V g hg
    rw [EEx_succ_bwd, demand_zero, EEx_pure]
    simp only [demand_zero, EEx_pure, Function.comp_apply]
    calc fV a (V - Pi.single a 1) r g (0, 0)
        = ∑ c, step wt V c * fV a (V - Pi.single a 1) r g (0, 0) := by
          rw [← Finset.sum_mul, step_sum_one, one_mul]
      _ ≤ ∑ c, step wt V c * fV a V r g (shf c (0, 0)) := by
          apply sum_le_avail wt hw V
          intro c hc
          simp only [fV]
          split_ifs with h1 h2
          · exact hg.1 (le_shf c _)
          · exfalso
            apply h2
            rw [shf_fst]
            simp only [Pi.sub_apply, Pi.single_eq_same, Pi.zero_apply] at h1
            by_cases hca : c = some a
            · rw [if_pos hca]
              have := hc a hca
              simp only [Pi.zero_apply]
              omega
            · rw [if_neg hca]
              simp only [Pi.zero_apply]
              omega
          · exact zero_le
          · exact le_rfl
  | succ m ih =>
    intro V g hg
    rw [EEx_succ_bwd wt m (V - Pi.single a 1), EEx_succ_bwd wt (m + 1) V]
    have hfinL : ∀ c, EEx (demand wt (sb1 (V - Pi.single a 1) c) m)
        (fV a (V - Pi.single a 1) r g ∘ shf c) ≠ ⊤ := by
      intro c
      obtain ⟨B, hB, hgB⟩ := hg.2.2
      refine ne_top_of_le_ne_top hB (EEx_le _ _ B (fun x => ?_))
      simp only [Function.comp_apply, fV]
      split_ifs
      · exact hgB _
      · exact zero_le
    have hfinR : ∀ c, EEx (demand wt (sb1 V c) (m + 1)) (fV a V r g ∘ shf c) ≠ ⊤ := by
      intro c
      obtain ⟨B, hB, hgB⟩ := hg.2.2
      refine ne_top_of_le_ne_top hB (EEx_le _ _ B (fun x => ?_))
      simp only [Function.comp_apply, fV]
      split_ifs
      · exact hgB _
      · exact zero_le
    -- the termwise comparison for available c ≠ some a (or any available c when V a ≠ 1)
    have hterm : ∀ c, (∀ i, c = some i → 0 < V i) →
        (∀ i, c = some i → 0 < (V - (Pi.single a 1 : Fin n → ℕ)) i) →
        EEx (demand wt (sb1 (V - Pi.single a 1) c) m) (fV a (V - Pi.single a 1) r g ∘ shf c) ≤
          EEx (demand wt (sb1 V c) (m + 1)) (fV a V r g ∘ shf c) := by
      intro c hc hc'
      rw [fV_shf a _ r g c hc', fV_shf a V r g c hc, sb1_sub_comm]
      exact ih (sb1 V c) (g ∘ shf c) (hg.comp c)
    by_cases hVa : V a = 1
    · have hq' : ∀ c, qq wt (V - Pi.single a 1) c = if c = some a then 0 else qq wt V c := by
        intro c
        rcases c with _ | i
        · rw [if_neg (show ¬ ((none : Option (Fin n)) = some a) by simp)]
          rfl
        · by_cases hi : i = a
          · subst hi
            rw [if_pos rfl]
            simp [qq, Pi.sub_apply, hVa]
          · rw [if_neg (show ¬ ((some i : Option (Fin n)) = some a) by simpa using hi)]
            simp only [qq, Pi.sub_apply, Pi.single_eq_of_ne hi, tsub_zero]
      simp only [step_eq wt hw]
      refine key_alg2 (some a) (qq wt V) (qq wt (V - Pi.single a 1)) (qq_nonneg wt hw V) hq'
        (Z_pos wt hw _) _ _ hfinL hfinR ?_ ?_
      · intro c hco hqc
        apply hterm
        · rintro i rfl
          by_contra hcon
          apply hqc
          simp only [qq, if_neg hcon]
        · rintro i rfl
          have hia : i ≠ a := fun h => hco (by rw [h])
          rw [Pi.sub_apply, Pi.single_eq_of_ne hia, tsub_zero]
          by_contra hcon
          apply hqc
          simp only [qq, if_neg hcon]
      · have hpos : 0 < V a := by omega
        show EEx (demand wt (sb1 V (some a)) (m + 1)) (fV a V r g ∘ shf (some a)) = _
        rw [fV_shf a V r g (some a) (by rintro i ⟨⟩; exact hpos), comp_shf_self hg.2.1]
        show EEx (demand wt (V - Pi.single a 1) (m + 1)) (fV a (V - Pi.single a 1) r g) = _
        rw [EEx_succ_bwd wt m (V - Pi.single a 1)]
        simp only [step_eq wt hw]
    · have hst : ∀ c, step wt (V - Pi.single a 1) c = step wt V c := by
        intro c
        rw [step_eq wt hw, step_eq wt hw, qq_congr wt (V - Pi.single a 1) V]
        intro i
        by_cases hi : i = a
        · subst hi
          rw [Pi.sub_apply, Pi.single_eq_same]
          constructor <;> intro h <;> omega
        · rw [Pi.sub_apply, Pi.single_eq_of_ne hi, tsub_zero]
      simp only [hst]
      apply sum_le_avail wt hw V
      intro c hc
      apply hterm c hc
      rintro i rfl
      have := hc i rfl
      by_cases hi : i = a
      · subst hi
        rw [Pi.sub_apply, Pi.single_eq_same]
        omega
      · rw [Pi.sub_apply, Pi.single_eq_of_ne hi, tsub_zero]
        exact this

theorem L_lem (wt wt' : Weights n) (hw : wt.Pos) (hw' : wt'.Pos) (a : Fin n) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hq : ∀ V c, qq wt' V c = if c = some a then (1 - ε) * qq wt V c else qq wt V c)
    (r : ℕ) (m : ℕ) :
    ∀ (V : Fin n → ℕ) (g : St n → ℝ≥0∞), Adm a g →
      EEx (demand wt V m) (fV a V r g) ≤ EEx (demand wt' V m) (fV a V r g) := by
  induction m with
  | zero =>
    intro V g _
    rw [demand_zero, demand_zero]
  | succ m ih =>
    intro V g hg
    have hfin : ∀ c, EEx (demand wt (sb1 V c) m) (fV a V r g ∘ shf c) ≠ ⊤ := by
      intro c
      obtain ⟨B, hB, hgB⟩ := hg.2.2
      refine ne_top_of_le_ne_top hB (EEx_le _ _ B (fun x => ?_))
      simp only [Function.comp_apply, fV]
      split_ifs
      · exact hgB _
      · exact zero_le
    rw [EEx_succ_bwd wt m V, EEx_succ_bwd wt' m V]
    calc ∑ c, step wt V c * EEx (demand wt (sb1 V c) m) (fV a V r g ∘ shf c)
        ≤ ∑ c, step wt' V c * EEx (demand wt (sb1 V c) m) (fV a V r g ∘ shf c) := by
          simp only [step_eq wt hw, step_eq wt' hw']
          refine key_alg (some a) (qq wt V) (qq wt' V) (qq_nonneg wt hw V) (Z_pos wt hw V)
            ε hε0 hε1 (hq V) _ hfin ?_
          by_cases hVa : V a = 0
          · left
            simp [qq, hVa]
          · right
            have hpos : 0 < V a := Nat.pos_of_ne_zero hVa
            show EEx (demand wt (sb1 V (some a)) m) (fV a V r g ∘ shf (some a)) ≤ _
            rw [fV_shf a V r g (some a) (by rintro i ⟨⟩; exact hpos), comp_shf_self hg.2.1]
            have := C_lem wt hw a r m V g hg
            rw [EEx_succ_bwd wt m V] at this
            simpa only [step_eq wt hw, sb1] using this
      _ ≤ ∑ c, step wt' V c * EEx (demand wt' (sb1 V c) m) (fV a V r g ∘ shf c) := by
          apply sum_le_avail wt' hw' V
          intro c hc
          rw [fV_shf a V r g c hc]
          exact ih (sb1 V c) (g ∘ shf c) (hg.comp c)

theorem Mono_lem (wt : Weights n) (m : ℕ) : ∀ (V : Fin n → ℕ) (g : St n → ℝ≥0∞), Monotone g →
    EEx (demand wt V m) g ≤ EEx (demand wt V (m + 1)) g := by
  induction m with
  | zero =>
    intro V g hg
    rw [EEx_succ_bwd, demand_zero, EEx_pure]
    simp only [demand_zero, EEx_pure, Function.comp_apply]
    calc g (0, 0) = ∑ c, step wt V c * g (0, 0) := by
          rw [← Finset.sum_mul, step_sum_one, one_mul]
      _ ≤ ∑ c, step wt V c * g (shf c (0, 0)) :=
          Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (hg (le_shf c _)) (zero_le))
  | succ m ih =>
    intro V g hg
    rw [EEx_succ_bwd wt m V, EEx_succ_bwd wt (m + 1) V]
    exact Finset.sum_le_sum (fun c _ =>
      mul_le_mul_of_nonneg_left (ih _ _ (hg.comp (shf_mono c))) (zero_le))

theorem L0_lem (wt wt' : Weights n) (hw : wt.Pos) (hw' : wt'.Pos) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hq : ∀ V c, qq wt' V c = if c = none then (1 - ε) * qq wt V c else qq wt V c) (m : ℕ) :
    ∀ (V : Fin n → ℕ) (g : St n → ℝ≥0∞), Monotone g → (∀ x y : St n, x.1 = y.1 → g x = g y) →
      (∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ x, g x ≤ B) →
      EEx (demand wt V m) g ≤ EEx (demand wt' V m) g := by
  induction m with
  | zero =>
    intro V g _ _ _
    rw [demand_zero, demand_zero]
  | succ m ih =>
    intro V g hg hg2 hgB
    obtain ⟨B, hB, hgB'⟩ := hgB
    have hfin : ∀ c, EEx (demand wt (sb1 V c) m) (g ∘ shf c) ≠ ⊤ := fun c =>
      ne_top_of_le_ne_top hB (EEx_le _ _ B (fun x => hgB' _))
    rw [EEx_succ_bwd wt m V, EEx_succ_bwd wt' m V]
    calc ∑ c, step wt V c * EEx (demand wt (sb1 V c) m) (g ∘ shf c)
        ≤ ∑ c, step wt' V c * EEx (demand wt (sb1 V c) m) (g ∘ shf c) := by
          simp only [step_eq wt hw, step_eq wt' hw']
          refine key_alg none (qq wt V) (qq wt' V) (qq_nonneg wt hw V) (Z_pos wt hw V)
            ε hε0 hε1 (hq V) _ hfin ?_
          right
          show EEx (demand wt (sb1 V none) m) (g ∘ shf none) ≤ _
          have e : g ∘ shf none = g := funext (fun x => hg2 _ _ rfl)
          rw [e]
          have := Mono_lem wt m V g hg
          rw [EEx_succ_bwd wt m V] at this
          simpa only [step_eq wt hw, sb1] using this
      _ ≤ ∑ c, step wt' V c * EEx (demand wt' (sb1 V c) m) (g ∘ shf c) := by
          refine Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left
            (ih _ _ (hg.comp (shf_mono c)) ?_ ⟨B, hB, fun x => hgB' _⟩) (zero_le))
          intro x y hxy
          simp only [Function.comp_apply]
          apply hg2
          rcases c with _ | i
          · exact hxy
          · show x.1 + Pi.single i 1 = y.1 + Pi.single i 1
            rw [hxy]

lemma demand_supp (wt : Weights n) (hw : wt.Pos) (V : Fin n → ℕ) (m : ℕ) :
    ∀ x, demand wt V m x ≠ 0 → x.1 ≤ V := by
  induction m with
  | zero =>
    intro x hx
    rw [demand_zero, PMF.pure_apply] at hx
    split_ifs at hx with h
    · subst h
      exact Pi.le_def.2 (fun j => Nat.zero_le _)
    · exact absurd rfl hx
  | succ m ih =>
    intro x hx
    have hx' : x ∈ (demand wt V (m + 1)).support := (PMF.mem_support_iff _ _).2 hx
    rw [demand_succ, PMF.mem_support_bind_iff] at hx'
    obtain ⟨y, hy, hxy⟩ := hx'
    rw [PMF.mem_support_map_iff] at hxy
    obtain ⟨c, hc, rfl⟩ := hxy
    have hyV := ih y ((PMF.mem_support_iff _ _).1 hy)
    rcases c with _ | i
    · exact hyV
    · have hi := avail_of_ne wt hw _ i ((PMF.mem_support_iff _ _).1 hc)
      rw [Pi.sub_apply] at hi
      rw [Pi.le_def]
      intro j
      show y.1 j + (Pi.single i 1 : Fin n → ℕ) j ≤ V j
      by_cases hj : j = i
      · subst hj
        rw [Pi.single_eq_same]
        omega
      · rw [Pi.single_eq_of_ne hj, add_zero]
        exact hyV j

lemma fV0 (wt : Weights n) (hw : wt.Pos) (a : Fin n) (U : Fin n → ℕ) (m : ℕ)
    (g : St n → ℝ≥0∞) : EEx (demand wt U m) (fV a U 0 g) = EEx (demand wt U m) g := by
  refine EEx_congr _ _ _ (fun x hx => ?_)
  simp only [fV]
  rw [if_pos (show 0 + x.1 a ≤ U a by rw [zero_add]; exact demand_supp wt hw U m x hx a)]

/-! ## Scaled weights -/

lemma sp_pos (wt : Weights n) (hw : wt.Pos) (a : Fin n) (ε : ℝ) (hε1 : ε < 1) :
    (scaleProd wt a ε).Pos := by
  refine ⟨hw.1, fun j => ?_⟩
  by_cases hj : j = a
  · rw [hj]
    show 0 < Function.update wt.w a ((1 - ε) * wt.w a) a
    rw [Function.update_self]
    exact mul_pos (by linarith) (hw.2 a)
  · show 0 < Function.update wt.w a ((1 - ε) * wt.w a) j
    rw [Function.update_of_ne hj]
    exact hw.2 j

lemma hq_sp (wt : Weights n) (a : Fin n) (ε : ℝ) : ∀ V c,
    qq (scaleProd wt a ε) V c = if c = some a then (1 - ε) * qq wt V c else qq wt V c := by
  intro V c
  rcases c with _ | i
  · rw [if_neg (show ¬ ((none : Option (Fin n)) = some a) by simp)]
    rfl
  · by_cases hi : i = a
    · subst hi
      rw [if_pos rfl]
      simp only [qq, scaleProd, Function.update_self]
      split_ifs <;> simp
    · rw [if_neg (show ¬ ((some i : Option (Fin n)) = some a) by simpa using hi)]
      simp only [qq, scaleProd, Function.update_of_ne hi]

lemma snp_pos (wt : Weights n) (hw : wt.Pos) (ε : ℝ) (hε1 : ε < 1) :
    (scaleNoPurchase wt ε).Pos :=
  ⟨mul_pos (by linarith) hw.1, hw.2⟩

lemma hq_snp (wt : Weights n) (ε : ℝ) : ∀ V c,
    qq (scaleNoPurchase wt ε) V c = if c = none then (1 - ε) * qq wt V c else qq wt V c := by
  intro V c
  rcases c with _ | i
  · rw [if_pos rfl]
    rfl
  · rw [if_neg (show ¬ ((some i : Option (Fin n)) = none) by simp)]
    rfl

/-! ## Expected sales -/

def Xf (i : Fin n) : St n → ℝ≥0∞ := fun x => ((x.1 i : ℕ) : ℝ≥0∞)

lemma expXm_eq (wt : Weights n) (U : Fin n → ℕ) (m : ℕ) (i : Fin n) :
    expXm wt U m i = (EEx (demand wt U m) (Xf i)).toReal := rfl

lemma EX_min (wt : Weights n) (hw : wt.Pos) (U : Fin n → ℕ) (m : ℕ) (i : Fin n) :
    EEx (demand wt U m) (Xf i) =
      EEx (demand wt U m) (fun x => ((min (x.1 i) (U i) : ℕ) : ℝ≥0∞)) := by
  refine EEx_congr _ _ _ (fun x hx => ?_)
  simp only [Xf]
  rw [min_eq_left (demand_supp wt hw U m x hx i)]

lemma EX_ne_top (wt : Weights n) (hw : wt.Pos) (U : Fin n → ℕ) (m : ℕ) (i : Fin n) :
    EEx (demand wt U m) (Xf i) ≠ ⊤ := by
  rw [EX_min wt hw]
  refine ne_top_of_le_ne_top (ENNReal.natCast_ne_top (U i)) (EEx_le _ _ _ (fun x => ?_))
  exact_mod_cast min_le_right _ _

lemma gmin_mono (U : Fin n → ℕ) (i : Fin n) :
    Monotone (fun x : St n => ((min (x.1 i) (U i) : ℕ) : ℝ≥0∞)) := by
  intro x y hxy
  show ((min (x.1 i) (U i) : ℕ) : ℝ≥0∞) ≤ ((min (y.1 i) (U i) : ℕ) : ℝ≥0∞)
  exact_mod_cast min_le_min ((Prod.le_def.1 hxy).1 i) le_rfl

lemma part_ii (wt wt' : Weights n) (hw : wt.Pos) (hw' : wt'.Pos) (a : Fin n) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hq : ∀ V c, qq wt' V c = if c = some a then (1 - ε) * qq wt V c else qq wt V c)
    (U : Fin n → ℕ) (m : ℕ) (i : Fin n) (hia : i ≠ a) :
    EEx (demand wt U m) (Xf i) ≤ EEx (demand wt' U m) (Xf i) := by
  have hg : Adm a (fun x : St n => ((min (x.1 i) (U i) : ℕ) : ℝ≥0∞)) := by
    refine ⟨gmin_mono U i, ?_, (U i : ℝ≥0∞), ENNReal.natCast_ne_top _, fun x => ?_⟩
    · intro x y hxy _
      simp only [hxy i hia]
    · show ((min (x.1 i) (U i) : ℕ) : ℝ≥0∞) ≤ (U i : ℝ≥0∞)
      exact_mod_cast min_le_right _ _
  rw [EX_min wt hw, EX_min wt' hw', ← fV0 wt hw a U m, ← fV0 wt' hw' a U m]
  exact L_lem wt wt' hw hw' a ε hε0 hε1 hq 0 m U _ hg

lemma fwd_a (wt : Weights n) (U : Fin n → ℕ) (m : ℕ) (a : Fin n) :
    EEx (demand wt U (m + 1)) (Xf a) =
      EEx (demand wt U m) (Xf a) + EEx (demand wt U m) (fun x => step wt (U - x.1) (some a)) := by
  rw [EEx_succ_fwd, ← EEx_add]
  congr 1
  funext x
  show ∑ c, step wt (U - x.1) c * Xf a (shf c x) = Xf a x + step wt (U - x.1) (some a)
  have h1 : ∀ c, Xf a (shf c x) = Xf a x + (if c = some a then 1 else 0) := by
    intro c
    simp only [Xf]
    rw [shf_fst, Nat.cast_add]
    split_ifs <;> simp
  have h2 : ∀ c, step wt (U - x.1) c * Xf a (shf c x) =
      step wt (U - x.1) c * Xf a x + (if c = some a then step wt (U - x.1) c else 0) := by
    intro c
    rw [h1 c, mul_add]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun c _ => h2 c), Finset.sum_add_distrib, ← Finset.sum_mul,
    step_sum_one, one_mul, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

noncomputable def gCR (wt : Weights n) (U : Fin n → ℕ) (a : Fin n) : St n → ℝ≥0∞ :=
  fun x => ENNReal.ofReal (1 / (wt.w0 + wt.wsum (insert a (inStock (U - x.1)))))

lemma gCR_adm (wt : Weights n) (hw : wt.Pos) (U : Fin n → ℕ) (a : Fin n) :
    Adm a (gCR wt U a) := by
  have hD : ∀ S : Finset (Fin n), wt.w0 ≤ wt.w0 + wt.wsum S := fun S =>
    le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => (hw.2 i).le))
  refine ⟨?_, ?_, ENNReal.ofReal (1 / wt.w0), ENNReal.ofReal_ne_top, fun x => ?_⟩
  · intro x y hxy
    simp only [gCR]
    apply ENNReal.ofReal_le_ofReal
    apply one_div_le_one_div_of_le (lt_of_lt_of_le hw.1 (hD _))
    apply add_le_add le_rfl
    unfold Weights.wsum
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · apply Finset.insert_subset_insert
      intro j hj
      simp only [inStock, Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply] at hj ⊢
      have hxj : x.1 j ≤ y.1 j := (Prod.le_def.1 hxy).1 j
      omega
    · intro j _ _
      exact (hw.2 j).le
  · intro x y hxy _
    simp only [gCR]
    have : insert a (inStock (U - x.1)) = insert a (inStock (U - y.1)) := by
      ext j
      by_cases hj : j = a
      · subst hj
        simp
      · simp only [Finset.mem_insert, hj, false_or, inStock, Finset.mem_filter,
          Finset.mem_univ, true_and, Pi.sub_apply, hxy j hj]
    rw [this]
  · simp only [gCR]
    apply ENNReal.ofReal_le_ofReal
    exact one_div_le_one_div_of_le hw.1 (hD _)

lemma lem13 (wt : Weights n) (hw : wt.Pos) (a : Fin n) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (U : Fin n → ℕ) (m : ℕ) :
    EEx (demand wt U m) (fun x => ENNReal.ofReal (choiceRatio wt U a x)) ≤
      EEx (demand (scaleProd wt a ε) U m) (fun x => ENNReal.ofReal (choiceRatio wt U a x)) := by
  have e : (fun x => ENNReal.ofReal (choiceRatio wt U a x)) = fV a U 1 (gCR wt U a) := by
    funext x
    simp only [choiceRatio, fV, gCR]
    by_cases h : 0 < (U - x.1) a
    · have h' : 1 + x.1 a ≤ U a := by rw [Pi.sub_apply] at h; omega
      rw [if_pos h, if_pos h', Finset.insert_eq_of_mem]
      simp only [inStock, Finset.mem_filter, Finset.mem_univ, true_and]
      exact h
    · have h' : ¬ (1 + x.1 a ≤ U a) := by rw [Pi.sub_apply] at h; omega
      rw [if_neg h, if_neg h', ENNReal.ofReal_zero]
  rw [e]
  exact L_lem wt _ hw (sp_pos wt hw a ε hε1) a ε hε0 hε1 (hq_sp wt a ε) 1 m U _
    (gCR_adm wt hw U a)

lemma P1 (wt : Weights n) (hw : wt.Pos) (a : Fin n) (ε : ℝ) (hε1 : ε < 1) (U : Fin n → ℕ)
    (x : St n) :
    ENNReal.ofReal (1 - ε) * step wt (U - x.1) (some a) =
      ENNReal.ofReal ((1 - ε) * wt.w a) * ENNReal.ofReal (choiceRatio wt U a x) := by
  rw [step_eq wt hw, ZZ_eq]
  unfold choiceRatio
  simp only [qq]
  split_ifs with h
  · rw [← ENNReal.ofReal_mul (show (0:ℝ) ≤ 1 - ε by linarith),
      ← ENNReal.ofReal_mul (mul_nonneg (show (0:ℝ) ≤ 1 - ε by linarith) (hw.2 a).le)]
    congr 1
    ring
  · simp

lemma P2 (wt : Weights n) (hw : wt.Pos) (a : Fin n) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (U : Fin n → ℕ) (x : St n) :
    ENNReal.ofReal ((1 - ε) * wt.w a) * ENNReal.ofReal (choiceRatio wt U a x) ≤
      step (scaleProd wt a ε) (U - x.1) (some a) := by
  have hw' := sp_pos wt hw a ε hε1
  have hD' := Z_pos _ hw' (U - x.1)
  rw [step_eq _ hw', ZZ_eq]
  rw [ZZ_eq] at hD'
  unfold choiceRatio
  simp only [qq]
  split_ifs with h
  · rw [← ENNReal.ofReal_mul (mul_nonneg (show (0:ℝ) ≤ 1 - ε by linarith) (hw.2 a).le)]
    apply ENNReal.ofReal_le_ofReal
    have hle : (scaleProd wt a ε).w0 + (scaleProd wt a ε).wsum (inStock (U - x.1)) ≤
        wt.w0 + wt.wsum (inStock (U - x.1)) := by
      have hj : ∀ j, (scaleProd wt a ε).w j ≤ wt.w j := by
        intro j
        by_cases hja : j = a
        · rw [hja]
          show Function.update wt.w a ((1 - ε) * wt.w a) a ≤ wt.w a
          rw [Function.update_self]
          nlinarith [hw.2 a]
        · show Function.update wt.w a ((1 - ε) * wt.w a) j ≤ wt.w j
          rw [Function.update_of_ne hja]
      have : (scaleProd wt a ε).wsum (inStock (U - x.1)) ≤ wt.wsum (inStock (U - x.1)) :=
        Finset.sum_le_sum (fun j _ => hj j)
      have h0 : (scaleProd wt a ε).w0 = wt.w0 := rfl
      linarith
    have hwa : (scaleProd wt a ε).w a = (1 - ε) * wt.w a := by
      show Function.update wt.w a ((1 - ε) * wt.w a) a = _
      rw [Function.update_self]
    rw [hwa, mul_one_div]
    exact div_le_div_of_nonneg_left (mul_nonneg (by linarith) (hw.2 a).le) hD' hle
  · simp

lemma part_i (wt : Weights n) (hw : wt.Pos) (a : Fin n) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (U : Fin n → ℕ) (m : ℕ) :
    ENNReal.ofReal (1 - ε) * EEx (demand wt U m) (Xf a) ≤
      EEx (demand (scaleProd wt a ε) U m) (Xf a) := by
  induction m with
  | zero =>
    rw [demand_zero, demand_zero, EEx_pure]
    simp [Xf]
  | succ m ih =>
    rw [fwd_a, fwd_a, mul_add]
    refine add_le_add ih ?_
    calc ENNReal.ofReal (1 - ε) * EEx (demand wt U m) (fun x => step wt (U - x.1) (some a))
        = EEx (demand wt U m) (fun x => ENNReal.ofReal (1 - ε) * step wt (U - x.1) (some a)) :=
          (EEx_const_mul _ _ _).symm
      _ = EEx (demand wt U m) (fun x => ENNReal.ofReal ((1 - ε) * wt.w a) *
            ENNReal.ofReal (choiceRatio wt U a x)) := by
          congr 1
          funext x
          exact P1 wt hw a ε hε1 U x
      _ = ENNReal.ofReal ((1 - ε) * wt.w a) *
            EEx (demand wt U m) (fun x => ENNReal.ofReal (choiceRatio wt U a x)) :=
          EEx_const_mul _ _ _
      _ ≤ ENNReal.ofReal ((1 - ε) * wt.w a) *
            EEx (demand (scaleProd wt a ε) U m) (fun x => ENNReal.ofReal (choiceRatio wt U a x)) :=
          mul_le_mul_of_nonneg_left (lem13 wt hw a ε hε0 hε1 U m) (zero_le)
      _ = EEx (demand (scaleProd wt a ε) U m) (fun x => ENNReal.ofReal ((1 - ε) * wt.w a) *
            ENNReal.ofReal (choiceRatio wt U a x)) :=
          (EEx_const_mul _ _ _).symm
      _ ≤ EEx (demand (scaleProd wt a ε) U m)
            (fun x => step (scaleProd wt a ε) (U - x.1) (some a)) :=
          EEx_mono _ _ _ (fun x => P2 wt hw a ε hε0 hε1 U x)

theorem T2 (wts : Weights n) (hw : wts.Pos) (pM : ℕ →₀ ℝ) (hM : IsLaw pM)
    (a : Fin n) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (U : Fin n → ℕ) :
    (1 - ε) * expX wts pM U a ≤ expX (scaleProd wts a ε) pM U a ∧
      ∀ i, i ≠ a → expX wts pM U i ≤ expX (scaleProd wts a ε) pM U i := by
  have hw' := sp_pos wts hw a ε hε1
  refine ⟨?_, fun i hia => ?_⟩
  · unfold expX
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun m _ => ?_)
    have h1 := part_i wts hw a ε hε0 hε1 U m
    have hfin := EX_ne_top (scaleProd wts a ε) hw' U m a
    rw [expXm_eq, expXm_eq]
    calc (1 - ε) * (pM m * (EEx (demand wts U m) (Xf a)).toReal)
        = pM m * (ENNReal.ofReal (1 - ε) * EEx (demand wts U m) (Xf a)).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (show (0:ℝ) ≤ 1 - ε by linarith)]
          ring
      _ ≤ pM m * (EEx (demand (scaleProd wts a ε) U m) (Xf a)).toReal :=
          mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hfin h1) (hM.1 m)
  · unfold expX
    refine Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_left ?_ (hM.1 m))
    rw [expXm_eq, expXm_eq]
    exact ENNReal.toReal_mono (EX_ne_top _ hw' U m i)
      (part_ii wts _ hw hw' a ε hε0 hε1 (hq_sp wts a ε) U m i hia)

theorem SNP (wts : Weights n) (hw : wts.Pos) (pM : ℕ →₀ ℝ) (hM : IsLaw pM)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (U : Fin n → ℕ) (i : Fin n) :
    expX wts pM U i ≤ expX (scaleNoPurchase wts ε) pM U i := by
  have hw' := snp_pos wts hw ε hε1
  unfold expX
  refine Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_left ?_ (hM.1 m))
  rw [expXm_eq, expXm_eq]
  refine ENNReal.toReal_mono (EX_ne_top _ hw' U m i) ?_
  rw [EX_min wts hw, EX_min _ hw']
  refine L0_lem wts _ hw hw' ε hε0 hε1 (hq_snp wts ε) m U _ (gmin_mono U i) ?_
    ⟨(U i : ℝ≥0∞), ENNReal.natCast_ne_top _, fun x => ?_⟩
  · intro x y hxy
    simp only [hxy]
  · show ((min (x.1 i) (U i) : ℕ) : ℝ≥0∞) ≤ (U i : ℝ≥0∞)
    exact_mod_cast min_le_right _ _

lemma expX_nonneg (wt : Weights n) (pM : ℕ →₀ ℝ) (hM : IsLaw pM) (U : Fin n → ℕ) (i : Fin n) :
    0 ≤ expX wt pM U i :=
  Finset.sum_nonneg (fun m _ => mul_nonneg (hM.1 m) ENNReal.toReal_nonneg)

noncomputable def Wk (wt : Weights n) (wd : Fin n → ℝ) (k : ℕ) : Weights n :=
  ⟨wt.w0, fun i => if i.val < k then wd i else wt.w i⟩

lemma iterate (wt : Weights n) (hw : wt.Pos) (wd : Fin n → ℝ) (hwd0 : ∀ i, 0 < wd i)
    (hwd : ∀ i, wd i ≤ wt.w i) (c : ℝ) (hc : ∀ i, c * wt.w i ≤ wd i)
    (pM : ℕ →₀ ℝ) (hM : IsLaw pM) (U : Fin n → ℕ) :
    ∀ i, c * expX wt pM U i ≤ expX ⟨wt.w0, wd⟩ pM U i := by
  have hWpos : ∀ k, (Wk wt wd k).Pos := by
    intro k
    refine ⟨hw.1, fun i => ?_⟩
    show 0 < (if i.val < k then wd i else wt.w i)
    split_ifs
    · exact hwd0 i
    · exact hw.2 i
  have claim : ∀ k, ∀ i : Fin n,
      (i.val < k → c * expX wt pM U i ≤ expX (Wk wt wd k) pM U i) ∧
      (k ≤ i.val → expX wt pM U i ≤ expX (Wk wt wd k) pM U i) := by
    intro k
    induction k with
    | zero =>
      intro i
      have hW0 : Wk wt wd 0 = wt := by
        cases wt
        simp [Wk]
      refine ⟨fun h => absurd h (Nat.not_lt_zero _), fun _ => ?_⟩
      rw [hW0]
    | succ k ih =>
      intro i
      by_cases hk : k < n
      · obtain ⟨j, hjk⟩ : ∃ j : Fin n, j.val = k := ⟨⟨k, hk⟩, rfl⟩
        obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 - wd j / wt.w j := ⟨_, rfl⟩
        have hwj := hw.2 j
        have hdiv1 : wd j / wt.w j ≤ 1 := (div_le_one hwj).2 (hwd j)
        have hdiv0 : 0 < wd j / wt.w j := div_pos (hwd0 j) hwj
        have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
        have hδ1 : δ < 1 := by rw [hδ]; linarith
        have hWs : Wk wt wd (k + 1) = scaleProd (Wk wt wd k) j δ := by
          simp only [Wk, scaleProd]
          congr 1
          funext i'
          simp only [Function.update_apply]
          by_cases hij : i' = j
          · rw [hij, if_pos rfl]
            have h1 : j.val < k + 1 := by omega
            have h2 : ¬ (j.val < k) := by omega
            rw [if_pos h1, if_neg h2, hδ, sub_sub_cancel, div_mul_cancel₀ _ hwj.ne']
          · rw [if_neg hij]
            have : i'.val ≠ k := fun h => hij (Fin.ext (by rw [h, hjk]))
            by_cases h1 : i'.val < k
            · rw [if_pos h1, if_pos (show i'.val < k + 1 by omega)]
            · rw [if_neg h1, if_neg (show ¬ (i'.val < k + 1) by omega)]
        have T := T2 (Wk wt wd k) (hWpos k) pM hM j δ hδ0 hδ1 U
        rw [hWs]
        refine ⟨fun hi => ?_, fun hi => ?_⟩
        · by_cases hij : i = j
          · rw [hij]
            have hE := expX_nonneg wt pM hM U j
            have hc' : c ≤ 1 - δ := by
              rw [hδ, sub_sub_cancel, le_div_iff₀ hwj]
              exact hc j
            have h1δ : 0 ≤ 1 - δ := by linarith
            calc c * expX wt pM U j ≤ (1 - δ) * expX wt pM U j :=
                  mul_le_mul_of_nonneg_right hc' hE
              _ ≤ (1 - δ) * expX (Wk wt wd k) pM U j :=
                  mul_le_mul_of_nonneg_left ((ih j).2 (by omega)) h1δ
              _ ≤ _ := T.1
          · have hik : i.val < k := by
              have : i.val ≠ k := fun h => hij (Fin.ext (by rw [h, hjk]))
              omega
            exact ((ih i).1 hik).trans (T.2 i hij)
        · have hij : i ≠ j := fun h => by rw [h] at hi; omega
          exact ((ih i).2 (by omega)).trans (T.2 i hij)
      · have hWe : Wk wt wd (k + 1) = Wk wt wd k := by
          simp only [Wk]
          congr 1
          funext i'
          have h1 : i'.val < k + 1 := by have := i'.isLt; omega
          have h2 : i'.val < k := by have := i'.isLt; omega
          simp only [h1, h2, if_true]
        rw [hWe]
        refine ⟨fun hi => (ih i).1 (by have := i.isLt; omega), fun hi => ?_⟩
        exfalso
        have := i.isLt
        omega
  intro i
  have hWn : Wk wt wd n = ⟨wt.w0, wd⟩ := by
    simp only [Wk]
    congr 1
    funext i'
    simp only [i'.isLt, if_true]
  have := (claim n i).1 i.isLt
  rwa [hWn] at this

lemma step_scale (wt wt' : Weights n) (hw : wt.Pos) (hw' : wt'.Pos) (s : ℝ) (hs : 0 < s)
    (h : ∀ V c, qq wt' V c = s * qq wt V c) : ∀ V, step wt' V = step wt V := by
  intro V
  ext c
  rw [step_eq wt' hw', step_eq wt hw]
  simp only [h V]
  rw [← Finset.mul_sum, mul_div_mul_left _ _ hs.ne']

lemma demand_congr (wt wt' : Weights n) (h : ∀ V, step wt' V = step wt V) (U : Fin n → ℕ) :
    ∀ m, demand wt' U m = demand wt U m := by
  intro m
  induction m with
  | zero => rw [demand_zero, demand_zero]
  | succ m ih => rw [demand_succ, demand_succ, ih]; simp only [h]

/-! ## Event probabilities -/

lemma prob_eq (wt : Weights n) (U : Fin n → ℕ) (m : ℕ) (A : Set (St n)) :
    prob wt U m A = (EEx (demand wt U m) (A.indicator 1)).toReal := by
  unfold prob EEx
  rw [PMF.toOuterMeasure_apply]
  congr 1
  refine tsum_congr (fun x => ?_)
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, mul_one]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]

lemma ind_le (A : Set (St n)) : ∀ x, A.indicator (1 : St n → ℝ≥0∞) x ≤ 1 := by
  intro x
  by_cases hx : x ∈ A
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

lemma ind_adm (a : Fin n) (A : Set (St n)) (hA : IsUpSetOff a A) :
    Adm a (A.indicator (1 : St n → ℝ≥0∞)) := by
  refine ⟨?_, ?_, 1, ENNReal.one_ne_top, ind_le A⟩
  · intro x y hxy
    by_cases hx : x ∈ A
    · simp [Set.indicator_of_mem hx, Set.indicator_of_mem (hA.1 hxy hx)]
    · simp [Set.indicator_of_notMem hx]
  · intro x y hxy h2
    by_cases hx : x ∈ A
    · simp [Set.indicator_of_mem hx, Set.indicator_of_mem (hA.2 x y hxy h2 hx)]
    · have hy : y ∉ A := fun hy => hx (hA.2 y x (fun j hj => (hxy j hj).symm) h2.symm hy)
      simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]

lemma C0_ind (wt : Weights n) (hw : wt.Pos) (a : Fin n) (A : Set (St n)) (hA : IsUpSetOff a A)
    (W : Fin n → ℕ) (k : ℕ) :
    EEx (demand wt (W - Pi.single a 1) k) (A.indicator 1) ≤
      EEx (demand wt W (k + 1)) (A.indicator 1) := by
  have := C_lem wt hw a 0 k W _ (ind_adm a A hA)
  rwa [fV0 wt hw a _ k, fV0 wt hw a _ (k + 1)] at this

/-! ## Removing one unit of a product -/

lemma key_alg3 {ι : Type*} [Fintype ι] [DecidableEq ι] (o : ι) (q q' : ι → ℝ)
    (hq : ∀ c, 0 ≤ q c) (hq' : ∀ c, q' c = if c = o then 0 else q c)
    (hZ' : 0 < ∑ c, q' c) (G L : ι → ℝ≥0∞) (hG : ∀ c, G c ≠ ⊤) (hL : ∀ c, L c ≠ ⊤)
    (hGL : ∀ c, c ≠ o → q c ≠ 0 → G c ≤ L c)
    (hGo : G o ≤ ∑ c, ENNReal.ofReal (q' c / ∑ d, q' d) * L c) :
    ∑ c, ENNReal.ofReal (q c / ∑ d, q d) * G c ≤
      ∑ c, ENNReal.ofReal (q' c / ∑ d, q' d) * L c := by
  have split : ∀ x : ι → ℝ, ∑ c, q c * x c = ∑ c, q' c * x c + q o * x o := by
    intro x
    have h1 : ∀ c, q c * x c = q' c * x c + (if c = o then q o * x o else 0) := by
      intro c
      rw [hq' c]
      split_ifs with h
      · subst h; ring
      · ring
    rw [Finset.sum_congr rfl (fun c _ => h1 c), Finset.sum_add_distrib, Finset.sum_ite_eq',
      if_pos (Finset.mem_univ _)]
  have hq'0 : ∀ c, 0 ≤ q' c := by
    intro c
    rw [hq' c]
    split_ifs
    · exact le_rfl
    · exact hq c
  have hZsplit : ∑ c, q c = ∑ c, q' c + q o := by
    have := split (fun _ => 1)
    simp only [mul_one] at this
    exact this
  have hZ : 0 < ∑ c, q c := by rw [hZsplit]; linarith [hq o]
  rw [sum_ofReal_mul _ (fun c => div_nonneg (hq c) hZ.le) G hG,
    sum_ofReal_mul _ (fun c => div_nonneg (hq'0 c) hZ'.le) L hL]
  rw [sum_ofReal_mul _ (fun c => div_nonneg (hq'0 c) hZ'.le) L hL] at hGo
  apply ENNReal.ofReal_le_ofReal
  have e1 : ∑ c, q' c / (∑ d, q' d) * (L c).toReal = (∑ c, q' c * (L c).toReal) / ∑ d, q' d := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    ring
  have e2 : ∑ c, q c / (∑ d, q d) * (G c).toReal = (∑ c, q c * (G c).toReal) / ∑ d, q d := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    ring
  have hgo : (G o).toReal * ∑ d, q' d ≤ ∑ c, q' c * (L c).toReal := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hGo
    rw [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun c _ =>
      mul_nonneg (div_nonneg (hq'0 c) hZ'.le) ENNReal.toReal_nonneg)), e1, le_div_iff₀ hZ'] at this
    exact this
  have hge : ∑ c, q' c * (G c).toReal ≤ ∑ c, q' c * (L c).toReal := by
    refine Finset.sum_le_sum (fun c _ => ?_)
    by_cases hco : c = o
    · rw [hq' c, if_pos hco, zero_mul, zero_mul]
    · by_cases hqc : q c = 0
      · rw [hq' c, if_neg hco, hqc, zero_mul, zero_mul]
      · exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (hL c) (hGL c hco hqc)) (hq'0 c)
  rw [e1, e2, div_le_div_iff₀ hZ hZ']
  calc (∑ c, q c * (G c).toReal) * ∑ d, q' d
      = (∑ c, q' c * (G c).toReal) * ∑ d, q' d + q o * ((G o).toReal * ∑ d, q' d) := by
        rw [split (fun c => (G c).toReal)]; ring
    _ ≤ (∑ c, q' c * (L c).toReal) * ∑ d, q' d + q o * (∑ c, q' c * (L c).toReal) := by
        have h1 := mul_le_mul_of_nonneg_right hge hZ'.le
        have h2 := mul_le_mul_of_nonneg_left hgo (hq o)
        linarith
    _ = (∑ c, q' c * (L c).toReal) * ∑ d, q d := by rw [hZsplit]; ring

noncomputable def fI (i : Fin n) (u : ℕ) (g : St n → ℝ≥0∞) : St n → ℝ≥0∞ :=
  fun x => if u ≤ x.1 i then g x else 0

lemma fI0 (i : Fin n) (g : St n → ℝ≥0∞) : fI i 0 g = g := by
  funext x
  simp [fI]

lemma fI_shf (i : Fin n) (u : ℕ) (g : St n → ℝ≥0∞) (c : Option (Fin n)) :
    fI i u g ∘ shf c = fI i (if c = some i then u - 1 else u) (g ∘ shf c) := by
  funext x
  simp only [Function.comp_apply, fI]
  rw [shf_fst]
  by_cases hc : c = some i
  · rw [if_pos hc, if_pos hc]
    by_cases h : u ≤ x.1 i + 1
    · rw [if_pos h, if_pos (show u - 1 ≤ x.1 i by omega)]
    · rw [if_neg h, if_neg (show ¬ (u - 1 ≤ x.1 i) by omega)]
  · rw [if_neg hc, if_neg hc, add_zero]

lemma fI_bound {i : Fin n} {u : ℕ} {g : St n → ℝ≥0∞} {B : ℝ≥0∞} (hB : ∀ x, g x ≤ B) :
    ∀ x, fI i u g x ≤ B := by
  intro x
  simp only [fI]
  split_ifs
  · exact hB x
  · exact zero_le

theorem Rem_lem (wt : Weights n) (hw : wt.Pos) (i : Fin n) (m : ℕ) :
    ∀ (V : Fin n → ℕ) (g : St n → ℝ≥0∞) (u : ℕ), Adm i g → (u = 0 ∨ u + 1 ≤ V i) →
      EEx (demand wt V m) (fI i u g) ≤ EEx (demand wt (V - Pi.single i 1) m) (fI i u g) := by
  induction m with
  | zero =>
    intro V g u _ _
    rw [demand_zero, demand_zero]
  | succ m ih =>
    intro V g u hg hu
    obtain ⟨B, hB, hgB⟩ := hg.2.2
    by_cases hV0 : V i = 0
    · have hVe : V - Pi.single i 1 = V := by
        funext j
        by_cases hj : j = i
        · subst hj
          rw [Pi.sub_apply, hV0, Nat.zero_sub]
        · rw [Pi.sub_apply, Pi.single_eq_of_ne hj, tsub_zero]
      rw [hVe]
    by_cases hV1 : V i = 1
    · have hu0 : u = 0 := by omega
      subst hu0
      rw [fI0]
      have hq' : ∀ c, qq wt (V - Pi.single i 1) c = if c = some i then 0 else qq wt V c := by
        intro c
        rcases c with _ | k
        · rw [if_neg (show ¬ ((none : Option (Fin n)) = some i) by simp)]
          rfl
        · by_cases hk : k = i
          · subst hk
            rw [if_pos rfl]
            simp [qq, Pi.sub_apply, hV1]
          · rw [if_neg (show ¬ ((some k : Option (Fin n)) = some i) by simpa using hk)]
            simp only [qq, Pi.sub_apply, Pi.single_eq_of_ne hk, tsub_zero]
      have hfinG : ∀ c, EEx (demand wt (sb1 V c) m) (g ∘ shf c) ≠ ⊤ := fun c =>
        ne_top_of_le_ne_top hB (EEx_le _ _ B (fun x => hgB _))
      have hfinL : ∀ c, EEx (demand wt (sb1 (V - Pi.single i 1) c) m) (g ∘ shf c) ≠ ⊤ :=
        fun c => ne_top_of_le_ne_top hB (EEx_le _ _ B (fun x => hgB _))
      rw [EEx_succ_bwd wt m V, EEx_succ_bwd wt m (V - Pi.single i 1)]
      simp only [step_eq wt hw]
      refine key_alg3 (some i) (qq wt V) (qq wt (V - Pi.single i 1)) (qq_nonneg wt hw V) hq'
        (Z_pos wt hw _) _ _ hfinG hfinL ?_ ?_
      · intro c hco hqc
        have h := ih (sb1 V c) (g ∘ shf c) 0 (hg.comp c) (Or.inl rfl)
        rw [fI0, ← sb1_sub_comm] at h
        exact h
      · show EEx (demand wt (sb1 V (some i)) m) (g ∘ shf (some i)) ≤ _
        rw [comp_shf_self hg.2.1]
        have h1 := Mono_lem wt m (V - Pi.single i 1) g hg.1
        rw [EEx_succ_bwd wt m (V - Pi.single i 1)] at h1
        simpa only [step_eq wt hw, sb1] using h1
    · -- V i ≥ 2: the first-step probabilities agree
      have hst : ∀ c, step wt (V - Pi.single i 1) c = step wt V c := by
        intro c
        rw [step_eq wt hw, step_eq wt hw, qq_congr wt (V - Pi.single i 1) V]
        intro j
        by_cases hj : j = i
        · subst hj
          rw [Pi.sub_apply, Pi.single_eq_same]
          constructor <;> intro h <;> omega
        · rw [Pi.sub_apply, Pi.single_eq_of_ne hj, tsub_zero]
      rw [EEx_succ_bwd wt m V, EEx_succ_bwd wt m (V - Pi.single i 1)]
      simp only [hst]
      apply sum_le_avail wt hw V
      intro c hc
      rw [fI_shf, sb1_sub_comm]
      refine ih (sb1 V c) (g ∘ shf c) _ (hg.comp c) ?_
      rcases c with _ | k
      · rw [if_neg (show ¬ ((none : Option (Fin n)) = some i) by simp)]
        exact hu
      · by_cases hk : k = i
        · subst hk
          rw [if_pos rfl]
          have := hc k rfl
          show (u - 1 = 0 ∨ u - 1 + 1 ≤ (V - (Pi.single k 1 : Fin n → ℕ)) k)
          rw [Pi.sub_apply, Pi.single_eq_same]
          omega
        · rw [if_neg (show ¬ ((some k : Option (Fin n)) = some i) by simpa using hk)]
          show (u = 0 ∨ u + 1 ≤ (V - (Pi.single k 1 : Fin n → ℕ)) i)
          rw [Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm hk), tsub_zero]
          exact hu

lemma chain (wt : Weights n) (m : ℕ) (g : St n → ℝ≥0∞) (V' V : Fin n → ℕ)
    (hstep : ∀ W k, V' ≤ W → W ≤ V → V' k < W k →
      EEx (demand wt W m) g ≤ EEx (demand wt (W - Pi.single k 1) m) g) :
    ∀ d (W : Fin n → ℕ), V' ≤ W → W ≤ V → ∑ k, (W k - V' k) = d →
      EEx (demand wt W m) g ≤ EEx (demand wt V' m) g := by
  intro d
  induction d with
  | zero =>
    intro W hW _ hd
    have : W = V' := by
      funext k
      have h1 := Finset.sum_eq_zero_iff.1 hd k (Finset.mem_univ _)
      have h2 : V' k ≤ W k := hW k
      omega
    rw [this]
  | succ d ih =>
    intro W hW hWV hd
    obtain ⟨k, hk⟩ : ∃ k, V' k < W k := by
      by_contra hcon
      push_neg at hcon
      have : ∑ k, (W k - V' k) = 0 :=
        Finset.sum_eq_zero (fun k _ => by have := hcon k; omega)
      omega
    have hW' : V' ≤ W - Pi.single k 1 := by
      refine Pi.le_def.2 (fun j => ?_)
      by_cases hj : j = k
      · subst hj
        rw [Pi.sub_apply, Pi.single_eq_same]
        omega
      · rw [Pi.sub_apply, Pi.single_eq_of_ne hj, tsub_zero]
        exact hW j
    have hWV' : W - Pi.single k 1 ≤ V := by
      refine Pi.le_def.2 (fun j => ?_)
      have h1 : W j ≤ V j := hWV j
      rw [Pi.sub_apply]
      omega
    refine (hstep W k hW hWV hk).trans (ih _ hW' hWV' ?_)
    have h1 : (W k - V' k) + ∑ j ∈ Finset.univ.erase k, (W j - V' j) = ∑ j, (W j - V' j) :=
      Finset.add_sum_erase Finset.univ (fun j => W j - V' j) (Finset.mem_univ k)
    have h2 : ((W - (Pi.single k 1 : Fin n → ℕ)) k - V' k) +
        ∑ j ∈ Finset.univ.erase k, ((W - (Pi.single k 1 : Fin n → ℕ)) j - V' j) =
          ∑ j, ((W - (Pi.single k 1 : Fin n → ℕ)) j - V' j) :=
      Finset.add_sum_erase Finset.univ (fun j => (W - (Pi.single k 1 : Fin n → ℕ)) j - V' j) (Finset.mem_univ k)
    have h3 : ∑ j ∈ Finset.univ.erase k, ((W - (Pi.single k 1 : Fin n → ℕ)) j - V' j) =
        ∑ j ∈ Finset.univ.erase k, (W j - V' j) :=
      Finset.sum_congr rfl (fun j hj => by
        rw [Pi.sub_apply, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hj), tsub_zero])
    have h4 : (W - (Pi.single k 1 : Fin n → ℕ)) k - V' k = W k - V' k - 1 := by
      rw [Pi.sub_apply, Pi.single_eq_same]
      omega
    omega

lemma EEx_finsum {α : Type*} (μ : PMF α) (s : Finset ℕ) (f : ℕ → α → ℝ≥0∞) :
    EEx μ (fun x => ∑ u ∈ s, f u x) = ∑ u ∈ s, EEx μ (f u) := by
  refine Finset.induction_on s ?_ ?_
  · simp [EEx]
  · intro a s ha ih
    simp only [Finset.sum_insert ha]
    rw [EEx_add, ih]

lemma EX_units (wt : Weights n) (hw : wt.Pos) (V : Fin n → ℕ) (m : ℕ) (i : Fin n) :
    EEx (demand wt V m) (Xf i) =
      ∑ u ∈ Finset.range (V i), EEx (demand wt V m) (fI i (u + 1) 1) := by
  rw [← EEx_finsum]
  refine EEx_congr _ _ _ (fun x hx => ?_)
  have hxi : x.1 i ≤ V i := demand_supp wt hw V m x hx i
  have hfilt : (Finset.range (V i)).filter (fun u => u + 1 ≤ x.1 i) = Finset.range (x.1 i) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  simp only [Xf, fI, Pi.one_apply]
  rw [Finset.sum_boole, hfilt, Finset.card_range]

lemma avg_le (a : ℕ → ℝ≥0∞) (ha : Antitone a) (c c' : ℕ) (hc : c' ≤ c) :
    (c' : ℝ≥0∞) * ∑ u ∈ Finset.range c, a u ≤ (c : ℝ≥0∞) * ∑ u ∈ Finset.range c', a u := by
  rw [← Finset.sum_range_add_sum_Ico a hc]
  have h1 : (c' : ℝ≥0∞) * a c' ≤ ∑ u ∈ Finset.range c', a u := by
    have := Finset.card_nsmul_le_sum (Finset.range c') a (a c')
      (fun u hu => ha (show u ≤ c' by simp only [Finset.mem_range] at hu; omega))
    simpa [nsmul_eq_mul] using this
  have h2 : ∑ u ∈ Finset.Ico c' c, a u ≤ ((c - c' : ℕ) : ℝ≥0∞) * a c' := by
    have := Finset.sum_le_card_nsmul (Finset.Ico c' c) a (a c')
      (fun u hu => ha (show c' ≤ u by simp only [Finset.mem_Ico] at hu; omega))
    simpa [nsmul_eq_mul] using this
  have hcc : (c : ℝ≥0∞) = (c' : ℝ≥0∞) + ((c - c' : ℕ) : ℝ≥0∞) := by
    rw [← Nat.cast_add]
    congr 1
    omega
  calc (c' : ℝ≥0∞) * (∑ u ∈ Finset.range c', a u + ∑ u ∈ Finset.Ico c' c, a u)
      = c' * ∑ u ∈ Finset.range c', a u + c' * ∑ u ∈ Finset.Ico c' c, a u := mul_add _ _ _
    _ ≤ c' * ∑ u ∈ Finset.range c', a u + c' * (((c - c' : ℕ) : ℝ≥0∞) * a c') := by gcongr
    _ = c' * ∑ u ∈ Finset.range c', a u + ((c - c' : ℕ) : ℝ≥0∞) * (c' * a c') := by ring
    _ ≤ c' * ∑ u ∈ Finset.range c', a u + ((c - c' : ℕ) : ℝ≥0∞) * ∑ u ∈ Finset.range c', a u := by
        gcongr
    _ = c * ∑ u ∈ Finset.range c', a u := by rw [hcc]; ring

lemma adm_one (i : Fin n) : Adm i (1 : St n → ℝ≥0∞) :=
  ⟨monotone_const, fun _ _ _ _ => rfl, 1, ENNReal.one_ne_top, fun _ => le_rfl⟩

lemma adm_fI (k i : Fin n) (hki : k ≠ i) (u : ℕ) : Adm k (fI i u (1 : St n → ℝ≥0∞)) := by
  refine ⟨?_, ?_, 1, ENNReal.one_ne_top, fI_bound (fun _ => le_rfl)⟩
  · intro x y hxy
    have hxi : x.1 i ≤ y.1 i := (Prod.le_def.1 hxy).1 i
    simp only [fI, Pi.one_apply]
    split_ifs with h1 h2
    · exact le_rfl
    · exfalso; omega
    · exact zero_le
    · exact le_rfl
  · intro x y hxy _
    simp only [fI, Pi.one_apply]
    rw [hxy i (Ne.symm hki)]

lemma adm_min (k j : Fin n) (hkj : k ≠ j) (B : ℕ) :
    Adm k (fun x : St n => ((min (x.1 j) B : ℕ) : ℝ≥0∞)) := by
  refine ⟨?_, ?_, (B : ℝ≥0∞), ENNReal.natCast_ne_top _, fun x => ?_⟩
  · intro x y hxy
    show ((min (x.1 j) B : ℕ) : ℝ≥0∞) ≤ ((min (y.1 j) B : ℕ) : ℝ≥0∞)
    exact_mod_cast min_le_min ((Prod.le_def.1 hxy).1 j) le_rfl
  · intro x y hxy _
    simp only [hxy j (Ne.symm hkj)]
  · show ((min (x.1 j) B : ℕ) : ℝ≥0∞) ≤ (B : ℝ≥0∞)
    exact_mod_cast min_le_right _ _

end Aux_MNLS0

open MNLStability Aux_MNLS0 in
theorem solution {n : ℕ} (wts : Weights n) (hw : wts.Pos) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (pM : ℕ →₀ ℝ) (hM : IsLaw pM) (I : Finset (Fin n)) (hI : wts.UniformOn I) (C : ℕ)
    (U : Fin n → ℕ) (hU : norm1 U ≤ C) (Uup : Fin n → ℕ) (hoff : ∀ i, i ∉ I → Uup i = U i)
    (h1 : ∀ i, i ∉ I → expX wts pM Uup i = expX wts pM U i)
    (h2 : ∑ i ∈ I, r i * expX wts pM U i ≤ ∑ i ∈ I, r i * expX wts pM Uup i)
    (h3 : norm1 Uup = norm1 U) (ε : ℝ) (hε : 0 < ε) (H : Finset ℕ) (hH : IsSpaced ε C H) :
    (∀ i, i ∉ I → expX wts pM U i ≤ expX wts pM (swap I U fun i => floorH H (Uup i)) i) ∧
      (1 - ε) * ∑ i ∈ I, r i * expX wts pM U i ≤
        ∑ i ∈ I, r i * expX wts pM (swap I U fun i => floorH H (Uup i)) i ∧
      norm1 (swap I U fun i => floorH H (Uup i)) ≤ norm1 U := by
  obtain ⟨U', hU'⟩ : ∃ U', U' = swap I U fun i => floorH H (Uup i) := ⟨_, rfl⟩
  rw [← hU']
  have hfl : ∀ c, floorH H c ≤ c := fun c =>
    Finset.sup_le (fun b hb => (Finset.mem_filter.1 hb).2)
  have hU'I : ∀ i, i ∈ I → U' i = floorH H (Uup i) := by
    intro i hi
    rw [hU']
    simp only [swap, if_pos hi]
  have hU'off : ∀ i, i ∉ I → U' i = Uup i := by
    intro i hi
    rw [hU']
    simp only [swap, if_neg hi]
    exact (hoff i hi).symm
  have hle : U' ≤ Uup := by
    refine Pi.le_def.2 (fun i => ?_)
    by_cases hi : i ∈ I
    · rw [hU'I i hi]
      exact hfl _
    · rw [hU'off i hi]
  have hX : ∀ (W : Fin n → ℕ) i, 0 ≤ expX wts pM W i := fun W i => expX_nonneg wts pM hM W i
  have hchain : ∀ m (g : St n → ℝ≥0∞), (∀ W k, U' ≤ W → W ≤ Uup → U' k < W k →
      EEx (demand wts W m) g ≤ EEx (demand wts (W - Pi.single k 1) m) g) →
      EEx (demand wts Uup m) g ≤ EEx (demand wts U' m) g := fun m g hs =>
    chain wts m g U' Uup hs _ Uup hle le_rfl rfl
  have hoffk : ∀ W k, U' ≤ W → W ≤ Uup → U' k < W k → k ∈ I := by
    intro W k hW hWU hk
    by_contra hkI
    have : W k ≤ Uup k := hWU k
    rw [hU'off k hkI] at hk
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [← h1 i hi]
    unfold expX
    refine Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_left ?_ (hM.1 m))
    rw [expXm_eq, expXm_eq]
    refine ENNReal.toReal_mono (EX_ne_top _ hw U' m i) ?_
    rw [EX_min wts hw Uup, EX_min wts hw U', hU'off i hi]
    refine hchain m _ (fun W k hW hWU hk => ?_)
    have hki : k ≠ i := fun h => hi (h ▸ hoffk W k hW hWU hk)
    have := Rem_lem wts hw k m W _ 0 (adm_min k i hki (Uup i)) (Or.inl rfl)
    rwa [fI0] at this
  · have hprod : ∀ i ∈ I, (1 - ε) * expX wts pM Uup i ≤ expX wts pM U' i := by
      intro i hi
      obtain ⟨c, hc⟩ : ∃ c, c = Uup i := ⟨_, rfl⟩
      obtain ⟨c', hc'⟩ : ∃ c', c' = U' i := ⟨_, rfl⟩
      have hcc : c' ≤ c := by rw [hc, hc']; exact hle i
      have hm : ∀ m, (c' : ℝ≥0∞) * EEx (demand wts Uup m) (Xf i) ≤
          (c : ℝ≥0∞) * EEx (demand wts U' m) (Xf i) := by
        intro m
        rw [EX_units wts hw Uup m i, EX_units wts hw U' m i, ← hc, ← hc']
        have hanti : Antitone (fun u => EEx (demand wts Uup m) (fI i (u + 1) 1)) := by
          intro u v huv
          refine EEx_mono _ _ _ (fun x => ?_)
          simp only [fI, Pi.one_apply]
          split_ifs <;> first | exact le_rfl | exact zero_le | (exfalso; omega)
        have hunit : ∀ u ∈ Finset.range c', EEx (demand wts Uup m) (fI i (u + 1) 1) ≤
            EEx (demand wts U' m) (fI i (u + 1) 1) := by
          intro u hu
          rw [Finset.mem_range] at hu
          refine hchain m _ (fun W k hW hWU hk => ?_)
          by_cases hki : k = i
          · rw [hki] at hk ⊢
            exact Rem_lem wts hw i m W 1 (u + 1) (adm_one i) (Or.inr (by omega))
          · have := Rem_lem wts hw k m W _ 0 (adm_fI k i hki (u + 1)) (Or.inl rfl)
            rwa [fI0] at this
        calc (c' : ℝ≥0∞) * ∑ u ∈ Finset.range c, EEx (demand wts Uup m) (fI i (u + 1) 1)
            ≤ (c : ℝ≥0∞) * ∑ u ∈ Finset.range c', EEx (demand wts Uup m) (fI i (u + 1) 1) :=
              avg_le _ hanti c c' hcc
          _ ≤ (c : ℝ≥0∞) * ∑ u ∈ Finset.range c', EEx (demand wts U' m) (fI i (u + 1) 1) := by
              gcongr with u hu
              exact hunit u hu
      have hmix : (c' : ℝ) * expX wts pM Uup i ≤ (c : ℝ) * expX wts pM U' i := by
        unfold expX
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_le_sum (fun m _ => ?_)
        rw [expXm_eq, expXm_eq]
        have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top c)
          (EX_ne_top _ hw U' m i)) (hm m)
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
          ENNReal.toReal_natCast] at this
        nlinarith [hM.1 m]
      by_cases hc0 : c = 0
      · have hz : expX wts pM Uup i = 0 := by
          unfold expX
          refine Finset.sum_eq_zero (fun m _ => ?_)
          rw [expXm_eq, EX_units wts hw Uup m i, ← hc, hc0, Finset.range_zero, Finset.sum_empty,
            ENNReal.toReal_zero, mul_zero]
        rw [hz, mul_zero]
        exact hX U' i
      · have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.2 hc0
        have hcC : c ≤ C := by
          rw [hc]
          calc Uup i ≤ norm1 Uup :=
                Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
            _ = norm1 U := h3
            _ ≤ C := hU
        have hsp := hH.2.2 c hc1 hcC
        have hc'eq : (floorH H c : ℝ) = c' := by rw [hc', hU'I i hi, hc]
        rw [hc'eq] at hsp
        have hcpos : (0 : ℝ) < c := by exact_mod_cast hc1
        have hE := hX Uup i
        have hE' := hX U' i
        have k1 : (1 - ε) * (c : ℝ) ≤ c / (1 + ε) := by
          rw [le_div_iff₀ (by linarith)]
          nlinarith [sq_nonneg ε]
        have k2 : (1 - ε) * c * expX wts pM Uup i ≤ c' * expX wts pM Uup i :=
          mul_le_mul_of_nonneg_right (k1.trans hsp) hE
        have k3 : (1 - ε) * expX wts pM Uup i * c ≤ expX wts pM U' i * c := by nlinarith
        exact le_of_mul_le_mul_right k3 hcpos
    by_cases hε1 : ε ≤ 1
    · calc (1 - ε) * ∑ i ∈ I, r i * expX wts pM U i
          ≤ (1 - ε) * ∑ i ∈ I, r i * expX wts pM Uup i :=
            mul_le_mul_of_nonneg_left h2 (by linarith)
        _ = ∑ i ∈ I, r i * ((1 - ε) * expX wts pM Uup i) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun i _ => by ring)
        _ ≤ ∑ i ∈ I, r i * expX wts pM U' i :=
            Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hprod i hi) (hr i))
    · push_neg at hε1
      have hA : 0 ≤ ∑ i ∈ I, r i * expX wts pM U i :=
        Finset.sum_nonneg (fun i _ => mul_nonneg (hr i) (hX U i))
      have hB : 0 ≤ ∑ i ∈ I, r i * expX wts pM U' i :=
        Finset.sum_nonneg (fun i _ => mul_nonneg (hr i) (hX U' i))
      nlinarith
  · calc norm1 U' ≤ norm1 Uup := Finset.sum_le_sum (fun i _ => hle i)
      _ = norm1 U := h3
