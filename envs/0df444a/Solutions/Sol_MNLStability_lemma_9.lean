-- Prove2me | solution 1 for MNLStability.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T23:49:16.410183+00:00
-- url     : https://prove2.me/submissions/9b61b44e-25ee-47f0-9ef6-2907210ac7c2

import Mathlib
import Definitions.Def_MNLStability_IsLaw
import Definitions.Def_MNLStability_expX
import Definitions.Def_MNLStability_opt
import Definitions.Def_MNLStability_swap
import Definitions.Def_MNLStability_IsPriceOrder
import Definitions.Def_MNLStability_IsSpaced
import Definitions.Def_MNLStability_Lam
import Definitions.Def_MNLStability_greedyLengths
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

/-! ## Own inventory and relabelling -/

lemma Own_lem (wt : Weights n) (hw : wt.Pos) (j : Fin n) (m : ℕ) : ∀ V : Fin n → ℕ,
    EEx (demand wt (V - Pi.single j 1) m) (Xf j) ≤ EEx (demand wt V m) (Xf j) := by
  induction m with
  | zero =>
    intro V
    rw [demand_zero, demand_zero]
  | succ m ih =>
    intro V
    by_cases hV0 : V j = 0
    · have hVe : V - Pi.single j 1 = V := by
        funext i
        by_cases hi : i = j
        · rw [hi, Pi.sub_apply, hV0, Nat.zero_sub]
        · rw [Pi.sub_apply, Pi.single_eq_of_ne hi, tsub_zero]
      rw [hVe]
    by_cases hV1 : V j = 1
    · have hz : EEx (demand wt (V - Pi.single j 1) (m + 1)) (Xf j) =
          EEx (demand wt (V - Pi.single j 1) (m + 1)) (fun _ => 0) := by
        refine EEx_congr _ _ _ (fun x hx => ?_)
        have h1 : x.1 j ≤ (V - (Pi.single j 1 : Fin n → ℕ)) j := demand_supp wt hw _ _ x hx j
        rw [Pi.sub_apply, Pi.single_eq_same, hV1] at h1
        have h0 : x.1 j = 0 := by omega
        simp only [Xf, h0, Nat.cast_zero]
      have hz' : EEx (demand wt (V - Pi.single j 1) (m + 1)) (fun _ => (0 : ℝ≥0∞)) = 0 := by
        simp [EEx]
      rw [hz, hz']
      exact zero_le
    · have hst : ∀ c, step wt (V - Pi.single j 1) c = step wt V c := by
        intro c
        rw [step_eq wt hw, step_eq wt hw, qq_congr wt (V - Pi.single j 1) V]
        intro i
        by_cases hi : i = j
        · rw [hi, Pi.sub_apply, Pi.single_eq_same]
          constructor <;> intro h <;> omega
        · rw [Pi.sub_apply, Pi.single_eq_of_ne hi, tsub_zero]
      rw [EEx_succ_bwd wt m V, EEx_succ_bwd wt m (V - Pi.single j 1)]
      simp only [hst]
      refine Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left ?_ zero_le)
      have e : ∀ W : Fin n → ℕ, EEx (demand wt W m) (Xf j ∘ shf c) =
          EEx (demand wt W m) (Xf j) + (if c = some j then 1 else 0) := by
        intro W
        have h1 : Xf j ∘ shf c =
            fun x => Xf j x + (fun _ => (if c = some j then 1 else 0 : ℝ≥0∞)) x := by
          funext x
          simp only [Function.comp_apply, Xf]
          rw [shf_fst, Nat.cast_add]
          split_ifs <;> simp
        rw [h1, EEx_add]
        congr 1
        unfold EEx
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      rw [e, e, sb1_sub_comm]
      gcongr
      exact ih (sb1 V c)

def phi (σ : Equiv.Perm (Fin n)) (x : St n) : St n := (x.1 ∘ σ, x.2)

lemma qq_perm (wt : Weights n) (σ : Equiv.Perm (Fin n)) (hσ : ∀ i, wt.w (σ i) = wt.w i)
    (V : Fin n → ℕ) (c : Option (Fin n)) : qq wt (V ∘ σ) c = qq wt V (c.map σ) := by
  rcases c with _ | i
  · rfl
  · show (if 0 < V (σ i) then wt.w i else 0) = (if 0 < V (σ i) then wt.w (σ i) else 0)
    rw [hσ]

lemma sumqq_perm (wt : Weights n) (σ : Equiv.Perm (Fin n)) (hσ : ∀ i, wt.w (σ i) = wt.w i)
    (V : Fin n → ℕ) : ∑ d, qq wt (V ∘ σ) d = ∑ d, qq wt V d := by
  simp only [qq_perm wt σ hσ V]
  exact Fintype.sum_equiv (Equiv.optionCongr σ) _ _ (fun d => rfl)

lemma step_perm (wt : Weights n) (hw : wt.Pos) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, wt.w (σ i) = wt.w i) (V : Fin n → ℕ) (c : Option (Fin n)) :
    step wt (V ∘ σ) c = step wt V (c.map σ) := by
  rw [step_eq wt hw, step_eq wt hw, sumqq_perm wt σ hσ V, qq_perm wt σ hσ V]

lemma sb1_perm (σ : Equiv.Perm (Fin n)) (V : Fin n → ℕ) (c : Option (Fin n)) :
    sb1 (V ∘ σ) c = sb1 V (c.map σ) ∘ σ := by
  rcases c with _ | i
  · rfl
  · funext x
    show V (σ x) - (Pi.single i 1 : Fin n → ℕ) x =
      V (σ x) - (Pi.single (σ i) 1 : Fin n → ℕ) (σ x)
    simp only [Pi.single_apply, σ.injective.eq_iff]

lemma shf_perm (σ : Equiv.Perm (Fin n)) (c : Option (Fin n)) (x : St n) :
    shf c (phi σ x) = phi σ (shf (c.map σ) x) := by
  rcases c with _ | i
  · rfl
  · refine Prod.ext ?_ rfl
    funext y
    show x.1 (σ y) + (Pi.single i 1 : Fin n → ℕ) y =
      x.1 (σ y) + (Pi.single (σ i) 1 : Fin n → ℕ) (σ y)
    simp only [Pi.single_apply, σ.injective.eq_iff]

theorem EEx_perm (wt : Weights n) (hw : wt.Pos) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, wt.w (σ i) = wt.w i) (m : ℕ) : ∀ (V : Fin n → ℕ) (f : St n → ℝ≥0∞),
    EEx (demand wt (V ∘ σ) m) f = EEx (demand wt V m) (f ∘ phi σ) := by
  induction m with
  | zero =>
    intro V f
    rw [demand_zero, demand_zero, EEx_pure, EEx_pure]
    rfl
  | succ m ih =>
    intro V f
    rw [EEx_succ_bwd wt m (V ∘ σ), EEx_succ_bwd wt m V]
    refine Fintype.sum_equiv (Equiv.optionCongr σ) _ _ (fun c => ?_)
    show _ = step wt V (c.map σ) *
      EEx (demand wt (sb1 V (c.map σ)) m) ((f ∘ phi σ) ∘ shf (c.map σ))
    rw [step_perm wt hw σ hσ, sb1_perm, ih]
    congr 2
    funext x
    simp only [Function.comp_apply]
    rw [shf_perm]

lemma expX_perm (wt : Weights n) (hw : wt.Pos) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, wt.w (σ i) = wt.w i) (pM : ℕ →₀ ℝ) (U : Fin n → ℕ) (i : Fin n) :
    expX wt pM (U ∘ σ) i = expX wt pM U (σ i) := by
  unfold expX
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [expXm_eq, expXm_eq, EEx_perm wt hw σ hσ m U]
  rfl

lemma sales_mono (wt : Weights n) (hw : wt.Pos) (j k : Fin n) (hjk : j ≠ k)
    (hwjk : wt.w j = wt.w k) (V : Fin n → ℕ) (hV : V k ≤ V j) (m : ℕ) :
    EEx (demand wt V m) (Xf k) ≤ EEx (demand wt V m) (Xf j) := by
  have hτ : ∀ i, wt.w (Equiv.swap j k i) = wt.w i := by
    intro i
    by_cases hij : i = j
    · rw [hij, Equiv.swap_apply_left, hwjk]
    · by_cases hik : i = k
      · rw [hik, Equiv.swap_apply_right, hwjk]
      · rw [Equiv.swap_apply_of_ne_of_ne hij hik]
  obtain ⟨d, hd⟩ : ∃ d, d = V j - V k := ⟨_, rfl⟩
  have hB : (V - d • Pi.single j 1) + d • Pi.single k 1 = V ∘ Equiv.swap j k := by
    funext i
    by_cases hij : i = j
    · rw [hij]
      simp only [Function.comp_apply, Equiv.swap_apply_left, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hjk, smul_eq_mul, mul_one,
        mul_zero, add_zero]
      omega
    · by_cases hik : i = k
      · rw [hik]
        simp only [Function.comp_apply, Equiv.swap_apply_right, Pi.add_apply, Pi.sub_apply,
          Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hjk), smul_eq_mul,
          mul_one, mul_zero, tsub_zero]
        omega
      · simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hij hik, Pi.add_apply,
          Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hik,
          smul_eq_mul, mul_zero, tsub_zero, add_zero]
  have hown : ∀ t : ℕ, EEx (demand wt (V - t • Pi.single j 1) m) (Xf j) ≤
      EEx (demand wt V m) (Xf j) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [succ_nsmul, ← tsub_tsub]
      exact (Own_lem wt hw j m _).trans ih
  obtain ⟨A, hA⟩ : ∃ A, A = V - d • Pi.single j 1 := ⟨_, rfl⟩
  rw [← hA] at hB
  have hG : Adm k (fun x : St n => ((min (x.1 j) (V j) : ℕ) : ℝ≥0∞)) :=
    adm_min k j (Ne.symm hjk) (V j)
  have hrem : ∀ t : ℕ, EEx (demand wt (A + t • Pi.single k 1) m)
      (fun x : St n => ((min (x.1 j) (V j) : ℕ) : ℝ≥0∞)) ≤
      EEx (demand wt A m) (fun x : St n => ((min (x.1 j) (V j) : ℕ) : ℝ≥0∞)) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [succ_nsmul, ← add_assoc]
      have h := Rem_lem wt hw k m (A + t • Pi.single k 1 + Pi.single k 1) _ 0 hG (Or.inl rfl)
      have e : A + t • Pi.single k 1 + Pi.single k 1 - Pi.single k 1 =
          A + t • Pi.single k 1 := by
        funext x
        simp only [Pi.add_apply, Pi.sub_apply, Nat.add_sub_cancel]
      rw [fI0, e] at h
      exact h.trans ih
  have hAj : A j ≤ V j := by
    rw [hA, Pi.sub_apply]
    omega
  have e1 : EEx (demand wt A m) (Xf j) =
      EEx (demand wt A m) (fun x : St n => ((min (x.1 j) (V j) : ℕ) : ℝ≥0∞)) :=
    EEx_congr _ _ _ (fun x hx => by
      simp only [Xf]
      rw [min_eq_left ((demand_supp wt hw A m x hx j).trans hAj)])
  have hBj : (V ∘ Equiv.swap j k) j ≤ V j := by
    simp only [Function.comp_apply, Equiv.swap_apply_left]
    exact hV
  have e2 : EEx (demand wt (V ∘ Equiv.swap j k) m) (Xf j) =
      EEx (demand wt (V ∘ Equiv.swap j k) m)
        (fun x : St n => ((min (x.1 j) (V j) : ℕ) : ℝ≥0∞)) :=
    EEx_congr _ _ _ (fun x hx => by
      simp only [Xf]
      rw [min_eq_left ((demand_supp wt hw _ m x hx j).trans hBj)])
  have hsym : EEx (demand wt (V ∘ Equiv.swap j k) m) (Xf j) = EEx (demand wt V m) (Xf k) := by
    rw [EEx_perm wt hw (Equiv.swap j k) hτ m V]
    congr 1
    funext x
    simp only [Function.comp_apply, Xf, phi, Equiv.swap_apply_left]
  rw [← hsym, e2, ← hB]
  calc _ ≤ EEx (demand wt A m) (fun x : St n => ((min (x.1 j) (V j) : ℕ) : ℝ≥0∞)) := hrem d
    _ = EEx (demand wt A m) (Xf j) := e1.symm
    _ ≤ EEx (demand wt V m) (Xf j) := by rw [hA]; exact hown d

lemma sales_expX (wt : Weights n) (hw : wt.Pos) (pM : ℕ →₀ ℝ) (hM : IsLaw pM) (j k : Fin n)
    (hwjk : wt.w j = wt.w k) (V : Fin n → ℕ) (hV : V k ≤ V j) :
    expX wt pM V k ≤ expX wt pM V j := by
  by_cases hjk : j = k
  · rw [hjk]
  unfold expX
  refine Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_left ?_ (hM.1 m))
  rw [expXm_eq, expXm_eq]
  exact ENNReal.toReal_mono (EX_ne_top _ hw V m j) (sales_mono wt hw j k hjk hwjk V hV m)

lemma exists_sort_perm (I : Finset (Fin n)) (ord : List (Fin n)) (hnd : ord.Nodup)
    (hmem : ∀ i, i ∈ ord ↔ i ∈ I) (U : Fin n → ℕ) :
    ∃ σ : Equiv.Perm (Fin n), (∀ x, x ∉ I → σ x = x) ∧
      ord.Pairwise (fun a b => U (σ b) ≤ U (σ a)) := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Finset (Equiv.Perm (Fin n)),
      S = Finset.univ.filter (fun σ => ∀ x, x ∉ I → σ x = x) := ⟨_, rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Fin n → ℕ, ψ = fun i => ord.length - ord.idxOf i := ⟨_, rfl⟩
  have h1S : (1 : Equiv.Perm (Fin n)) ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun x _ => rfl⟩
  obtain ⟨σ, hσS, hmax⟩ := Finset.exists_max_image S (fun σ => ∑ i, ψ i * U (σ i)) ⟨1, h1S⟩
  have hσfix : ∀ x, x ∉ I → σ x = x := by
    rw [hS, Finset.mem_filter] at hσS
    exact hσS.2
  refine ⟨σ, hσfix, ?_⟩
  rw [List.pairwise_iff_getElem]
  intro p q hp hq hpq
  by_contra hcon
  push_neg at hcon
  obtain ⟨a, ha⟩ : ∃ a, a = ord[p] := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = ord[q] := ⟨_, rfl⟩
  rw [← ha, ← hb] at hcon
  have hia : ord.idxOf a = p := by rw [ha]; exact hnd.idxOf_getElem p hp
  have hib : ord.idxOf b = q := by rw [hb]; exact hnd.idxOf_getElem q hq
  have hab : a ≠ b := by
    intro h
    rw [h] at hia
    omega
  have haI : a ∈ I := (hmem a).1 (by rw [ha]; exact List.getElem_mem hp)
  have hbI : b ∈ I := (hmem b).1 (by rw [hb]; exact List.getElem_mem hq)
  have hψab : ψ b < ψ a := by
    rw [hψ]
    show ord.length - ord.idxOf b < ord.length - ord.idxOf a
    rw [hia, hib]
    omega
  have hτS : σ * Equiv.swap a b ∈ S := by
    rw [hS, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun x hx => ?_⟩
    have hxa : x ≠ a := fun h => hx (h ▸ haI)
    have hxb : x ≠ b := fun h => hx (h ▸ hbI)
    show σ (Equiv.swap a b x) = x
    rw [Equiv.swap_apply_of_ne_of_ne hxa hxb, hσfix x hx]
  have key : ∀ f : Fin n → ℕ,
      ∑ i, f i = f a + f b + ∑ i ∈ (Finset.univ.erase a).erase b, f i := by
    intro f
    rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ a),
      ← Finset.add_sum_erase (Finset.univ.erase a) f
        (Finset.mem_erase.2 ⟨Ne.symm hab, Finset.mem_univ b⟩), add_assoc]
  have hrest : ∑ i ∈ (Finset.univ.erase a).erase b, ψ i * U ((σ * Equiv.swap a b) i) =
      ∑ i ∈ (Finset.univ.erase a).erase b, ψ i * U (σ i) := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have hxb : x ≠ b := Finset.ne_of_mem_erase hx
    have hxa : x ≠ a := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hx)
    show ψ x * U (σ (Equiv.swap a b x)) = ψ x * U (σ x)
    rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
  have hτa : (σ * Equiv.swap a b) a = σ b := by
    show σ (Equiv.swap a b a) = σ b
    rw [Equiv.swap_apply_left]
  have hτb : (σ * Equiv.swap a b) b = σ a := by
    show σ (Equiv.swap a b b) = σ a
    rw [Equiv.swap_apply_right]
  have h1 : ∑ i, ψ i * U (σ i) = ψ a * U (σ a) + ψ b * U (σ b) +
      ∑ i ∈ (Finset.univ.erase a).erase b, ψ i * U (σ i) := key (fun i => ψ i * U (σ i))
  have h2 : ∑ i, ψ i * U ((σ * Equiv.swap a b) i) =
      ψ a * U ((σ * Equiv.swap a b) a) + ψ b * U ((σ * Equiv.swap a b) b) +
      ∑ i ∈ (Finset.univ.erase a).erase b, ψ i * U ((σ * Equiv.swap a b) i) :=
    key (fun i => ψ i * U ((σ * Equiv.swap a b) i))
  have hle : ∑ i, ψ i * U ((σ * Equiv.swap a b) i) ≤ ∑ i, ψ i * U (σ i) := hmax _ hτS
  rw [h1, h2, hrest, hτa, hτb] at hle
  nlinarith


/-! ## Unit probabilities -/

lemma ind_eq_fI (i : Fin n) (u : ℕ) :
    ({x : St n | u ≤ x.1 i}).indicator (1 : St n → ℝ≥0∞) = fI i u 1 := by
  funext x
  by_cases h : u ≤ x.1 i
  · rw [Set.indicator_of_mem (show x ∈ {x : St n | u ≤ x.1 i} from h)]
    simp [fI, h]
  · rw [Set.indicator_of_notMem (show x ∉ {x : St n | u ≤ x.1 i} from h)]
    simp [fI, h]

lemma unitProb_eq (wt : Weights n) (pM : ℕ →₀ ℝ) (U : Fin n → ℕ) (i : Fin n) :
    unitProb wt pM U i 1 =
      ∑ m ∈ pM.support, pM m * (EEx (demand wt U m) (fI i 1 1)).toReal := by
  unfold unitProb probM
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [prob_eq, ind_eq_fI]

lemma fI_one_ne_top (wt : Weights n) (U : Fin n → ℕ) (m : ℕ) (i : Fin n) (u : ℕ) :
    EEx (demand wt U m) (fI i u 1) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (EEx_le _ _ 1 (fI_bound (fun _ => le_rfl)))

lemma unitProb_nonneg (wt : Weights n) (pM : ℕ →₀ ℝ) (hM : IsLaw pM) (U : Fin n → ℕ)
    (i : Fin n) : 0 ≤ unitProb wt pM U i 1 := by
  rw [unitProb_eq]
  exact Finset.sum_nonneg (fun m _ => mul_nonneg (hM.1 m) ENNReal.toReal_nonneg)

lemma P_le_E (wt : Weights n) (hw : wt.Pos) (pM : ℕ →₀ ℝ) (hM : IsLaw pM) (U : Fin n → ℕ)
    (i : Fin n) : unitProb wt pM U i 1 ≤ expX wt pM U i := by
  rw [unitProb_eq]
  unfold expX
  refine Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_left ?_ (hM.1 m))
  rw [expXm_eq]
  refine ENNReal.toReal_mono (EX_ne_top _ hw U m i) (EEx_mono _ _ _ (fun x => ?_))
  simp only [fI, Xf, Pi.one_apply]
  split_ifs with h
  · exact_mod_cast h
  · exact zero_le

lemma E_le_UP (wt : Weights n) (hw : wt.Pos) (pM : ℕ →₀ ℝ) (hM : IsLaw pM) (U : Fin n → ℕ)
    (i : Fin n) : expX wt pM U i ≤ (U i : ℝ) * unitProb wt pM U i 1 := by
  rw [unitProb_eq, Finset.mul_sum]
  unfold expX
  refine Finset.sum_le_sum (fun m _ => ?_)
  rw [expXm_eq]
  have h1 : EEx (demand wt U m) (Xf i) ≤ (U i : ℝ≥0∞) * EEx (demand wt U m) (fI i 1 1) := by
    rw [EX_units wt hw U m i]
    have := Finset.sum_le_card_nsmul (Finset.range (U i))
      (fun u => EEx (demand wt U m) (fI i (u + 1) 1)) (EEx (demand wt U m) (fI i 1 1))
      (fun u _ => EEx_mono _ _ _ (fun x => by
        simp only [fI, Pi.one_apply]
        split_ifs <;> first | exact le_rfl | exact zero_le | (exfalso; omega)))
    simpa [nsmul_eq_mul] using this
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    (fI_one_ne_top wt U m i 1)) h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h2
  have h3 := hM.1 m
  nlinarith

lemma hMin_facts (wt : Weights n) (r : Fin n → ℝ) (pM : ℕ →₀ ℝ) (I : Finset (Fin n))
    (H : Finset ℕ) (U : Fin n → ℕ) (hpos : ∃ h ∈ H, 0 < Rlev wt r pM I U h) :
    hMin wt r pM I H U ∈ H ∧ 0 < Rlev wt r pM I U (hMin wt r pM I H U) := by
  obtain ⟨h0, hh0, hR0⟩ := hpos
  have hne : (H.filter (fun h => 0 < Rlev wt r pM I U h)).Nonempty :=
    ⟨h0, Finset.mem_filter.2 ⟨hh0, hR0⟩⟩
  obtain ⟨hm, hmmem, hmeq⟩ := Finset.exists_mem_eq_sup _ hne id
  have e : hMin wt r pM I H U = hm := hmeq
  rw [e]
  exact Finset.mem_filter.1 hmmem

lemma le_hMin (wt : Weights n) (r : Fin n → ℝ) (pM : ℕ →₀ ℝ) (I : Finset (Fin n))
    (H : Finset ℕ) (U : Fin n → ℕ) (h : ℕ) (hh : h ∈ H) (hR : 0 < Rlev wt r pM I U h) :
    h ≤ hMin wt r pM I H U :=
  Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨hh, hR⟩)


/-! ## Greedy reconstruction -/

lemma find_range (p : ℕ → Bool) (m : ℕ) (hm : p m = true) : ∀ N, m < N →
    ∃ k, (List.range N).find? p = some k ∧ k ≤ m := by
  intro N
  induction N with
  | zero => intro h; omega
  | succ N ih =>
    intro h
    rw [List.range_succ, List.find?_append]
    by_cases hmN : m < N
    · obtain ⟨k, hk, hkm⟩ := ih hmN
      exact ⟨k, by simp [hk], hkm⟩
    · have hmeq : m = N := by omega
      cases hf : (List.range N).find? p with
      | none =>
        refine ⟨N, ?_, by omega⟩
        subst hmeq
        simp [List.find?, hm]
      | some k =>
        refine ⟨k, by simp, ?_⟩
        have := List.mem_of_find?_eq_some hf
        rw [List.mem_range] at this
        omega

lemma leastPrefix_le' (rs : List ℝ) (τ : ℝ) (m : ℕ) (hm : m ≤ rs.length)
    (hτ : τ ≤ (rs.take m).sum) :
    ∃ k, leastPrefix rs τ = some k ∧ k ≤ m ∧ τ ≤ (rs.take k).sum := by
  unfold leastPrefix
  obtain ⟨k, hk, hkm⟩ := find_range (fun k => decide (τ ≤ (rs.take k).sum)) m
    (decide_eq_true hτ) (rs.length + 1) (by omega)
  refine ⟨k, hk, hkm, ?_⟩
  have := List.find?_some hk
  simpa using this

lemma take_sum_tail (ys : List ℝ) (hys : ys.Pairwise (fun a b => b ≤ a)) :
    ∀ m, m < ys.length → (ys.tail.take m).sum ≤ (ys.take m).sum := by
  induction ys with
  | nil => intro m h; simp at h
  | cons a t ih =>
    intro m hm
    rw [List.pairwise_cons] at hys
    cases m with
    | zero => simp
    | succ m =>
      cases t with
      | nil => simp at hm
      | cons b t' =>
        have hab : b ≤ a := hys.1 b (by simp)
        have h1 := ih hys.2 m (by simp only [List.length_cons] at hm ⊢; omega)
        simp only [List.tail_cons] at h1
        simp only [List.tail_cons, List.take_succ_cons, List.sum_cons]
        linarith

lemma drop_take_mono (xs : List ℝ) (hxs : xs.Pairwise (fun a b => b ≤ a)) (m s : ℕ) :
    ∀ d, s + d + m ≤ xs.length →
      ((xs.drop (s + d)).take m).sum ≤ ((xs.drop s).take m).sum := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro h
    have h1 := ih (by omega)
    have h2 : ((xs.drop (s + (d + 1))).take m).sum ≤ ((xs.drop (s + d)).take m).sum := by
      have hp : (xs.drop (s + d)).Pairwise (fun a b => b ≤ a) :=
        hxs.sublist (List.drop_sublist _ _)
      have := take_sum_tail (xs.drop (s + d)) hp m (by rw [List.length_drop]; omega)
      rwa [List.tail_drop, show s + d + 1 = s + (d + 1) by omega] at this
    linarith

lemma count_le (p q s : Fin n → Bool) (hpq : ∀ x, p x = true → q x = true → False)
    (hs : ∀ x, p x = true ∨ q x = true → s x = true) : ∀ L : List (Fin n),
    (L.filter p).length + (L.filter q).length ≤ (L.filter s).length
  | [] => by simp
  | a :: L => by
    have ih := count_le p q s hpq hs L
    have h1 := hpq a
    have h2 := hs a
    simp only [List.filter_cons]
    split_ifs <;> (try simp only [List.length_cons]) <;> first | omega | (exfalso; tauto)

lemma decomp (U : Fin n → ℕ) (h : ℕ) : ∀ L : List (Fin n), L.Pairwise (fun i j => U j ≤ U i) →
    L.filter (fun i => h < U i) ++ (L.filter (fun i => U i = h) ++ L.filter (fun i => U i < h))
      = L
  | [], _ => rfl
  | a :: L, hL => by
    rw [List.pairwise_cons] at hL
    have ih := decomp U h L hL.2
    have hle : ∀ b ∈ L, U b ≤ U a := hL.1
    rcases lt_trichotomy h (U a) with h1 | h1 | h1
    · have e1 : ¬ U a = h := by omega
      have e2 : ¬ U a < h := by omega
      rw [List.filter_cons_of_pos (p := fun i => decide (h < U i)) (a := a) (l := L)
          (by simpa using h1),
        List.filter_cons_of_neg (p := fun i => decide (U i = h)) (a := a) (l := L)
          (by simpa using e1),
        List.filter_cons_of_neg (p := fun i => decide (U i < h)) (a := a) (l := L)
          (by simpa using e2),
        List.cons_append, ih]
    · have e0 : ¬ h < U a := by omega
      have e2 : ¬ U a < h := by omega
      have hP : L.filter (fun i => h < U i) = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb
        have := hle b hb
        simp only [decide_eq_true_eq]
        omega
      rw [List.filter_cons_of_neg (p := fun i => decide (h < U i)) (a := a) (l := L)
          (by simpa using e0),
        List.filter_cons_of_pos (p := fun i => decide (U i = h)) (a := a) (l := L)
          (by simpa using h1.symm),
        List.filter_cons_of_neg (p := fun i => decide (U i < h)) (a := a) (l := L)
          (by simpa using e2)]
      rw [hP, List.nil_append] at ih
      rw [hP, List.nil_append, List.cons_append, ih]
    · have e0 : ¬ h < U a := by omega
      have e1 : ¬ U a = h := by omega
      have hP : L.filter (fun i => h < U i) = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb
        have := hle b hb
        simp only [decide_eq_true_eq]
        omega
      have hM : L.filter (fun i => U i = h) = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb
        have := hle b hb
        simp only [decide_eq_true_eq]
        omega
      rw [List.filter_cons_of_neg (p := fun i => decide (h < U i)) (a := a) (l := L)
          (by simpa using e0),
        List.filter_cons_of_neg (p := fun i => decide (U i = h)) (a := a) (l := L)
          (by simpa using e1),
        List.filter_cons_of_pos (p := fun i => decide (U i < h)) (a := a) (l := L)
          (by simpa using h1)]
      rw [hP, hM, List.nil_append, List.nil_append] at ih
      rw [hP, hM, List.nil_append, List.nil_append, ih]

def Acnt (L : List (Fin n)) (U : Fin n → ℕ) (h : ℕ) : ℕ := (L.filter (fun i => h < U i)).length

def Mcnt (L : List (Fin n)) (U : Fin n → ℕ) (h : ℕ) : ℕ := (L.filter (fun i => U i = h)).length

lemma pos_ge (L : List (Fin n)) (U : Fin n → ℕ) (hL : L.Pairwise (fun i j => U j ≤ U i))
    (h t : ℕ) (ht : t < Acnt L U h + Mcnt L U h) (htL : t < L.length) : h ≤ U L[t] := by
  have hdec := decomp U h L hL
  obtain ⟨P, hP⟩ : ∃ P, P = L.filter (fun i => h < U i) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = L.filter (fun i => U i = h) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = L.filter (fun i => U i < h) := ⟨_, rfl⟩
  rw [← hP, ← hM, ← hQ] at hdec
  have hA : Acnt L U h = P.length := by rw [hP]; rfl
  have hMc : Mcnt L U h = M.length := by rw [hM]; rfl
  have htake : L.take (P.length + M.length) = P ++ M := by
    rw [← hdec, ← List.append_assoc]
    exact List.take_left' (List.length_append)
  have hmem : L[t] ∈ L.take (P.length + M.length) := by
    have hlt : t < (L.take (P.length + M.length)).length := by
      rw [List.length_take]
      omega
    have := List.getElem_mem hlt
    rwa [List.getElem_take] at this
  rw [htake] at hmem
  rcases List.mem_append.1 hmem with h1 | h1
  · rw [hP, List.mem_filter, decide_eq_true_eq] at h1
    exact h1.2.le
  · rw [hM, List.mem_filter, decide_eq_true_eq] at h1
    exact h1.2.ge

def flatL (lv ks : List ℕ) : List ℕ := (lv.zip ks).flatMap (fun p => List.replicate p.2 p.1)

lemma flatL_nil : flatL [] [] = [] := rfl

lemma flatL_cons (ℓ k : ℕ) (lv ks : List ℕ) :
    flatL (ℓ :: lv) (k :: ks) = List.replicate k ℓ ++ flatL lv ks := by
  simp [flatL]

noncomputable def Ssum (e : ℕ → ℝ) (rs : List ℝ) (F : List ℕ) : ℝ :=
  (List.zipWith (fun a ℓ => a * e ℓ) rs F).sum

lemma Ssum_rep (e : ℕ → ℝ) (ℓ : ℕ) : ∀ xs : List ℝ,
    (List.zipWith (fun a ℓ' => a * e ℓ') xs (List.replicate xs.length ℓ)).sum = e ℓ * xs.sum
  | [] => by simp
  | x :: xs => by
    rw [List.length_cons, List.replicate_succ, List.zipWith_cons_cons, List.sum_cons,
      Ssum_rep e ℓ xs, List.sum_cons]
    ring

lemma Ssum_app (e : ℕ → ℝ) (rs : List ℝ) (ℓ k : ℕ) (F : List ℕ) (hk : k ≤ rs.length) :
    Ssum e rs (List.replicate k ℓ ++ F) = e ℓ * (rs.take k).sum + Ssum e (rs.drop k) F := by
  unfold Ssum
  have hlen : (rs.take k).length = k := by rw [List.length_take]; omega
  conv_lhs => rw [← List.take_append_drop k rs]
  rw [List.zipWith_append (by rw [hlen, List.length_replicate]), List.sum_append]
  congr 1
  have := Ssum_rep e ℓ (rs.take k)
  rwa [hlen] at this

lemma greedy9 (L : List (Fin n)) (U : Fin n → ℕ) (ρ : Fin n → ℝ) (τ e β : ℕ → ℝ)
    (hL : L.Pairwise (fun i j => U j ≤ U i)) (hρ : (L.map ρ).Pairwise (fun a b => b ≤ a))
    (hρ0 : ∀ i, 0 ≤ ρ i) :
    ∀ levels : List ℕ, levels.Pairwise (fun a b => b < a) →
    (∀ h ∈ levels, τ h ≤ ((L.filter (fun i => U i = h)).map ρ).sum) →
    (∀ h ∈ levels, ∀ x : ℝ, 0 ≤ x → τ h ≤ x → β h ≤ e h * x) →
    ∀ s, s ≤ L.length → (∀ h ∈ levels, s ≤ Acnt L U h) →
    ∃ ks, greedyLengths ((L.map ρ).drop s) (levels.map τ) = some ks ∧
      s + (flatL levels ks).length ≤ L.length ∧
      (∀ t (ht : t < (flatL levels ks).length) (hs : s + t < L.length),
        (flatL levels ks)[t] ≤ U L[s + t]) ∧
      (∀ x ∈ flatL levels ks, x ∈ levels) ∧
      (levels.map β).sum ≤ Ssum e ((L.map ρ).drop s) (flatL levels ks) := by
  intro levels
  induction levels with
  | nil =>
    intro _ _ _ s hsL _
    refine ⟨[], rfl, ?_, ?_, ?_, ?_⟩
    · rw [flatL_nil, List.length_nil, add_zero]
      exact hsL
    · intro t ht
      simp [flatL_nil] at ht
    · intro x hx
      simp [flatL_nil] at hx
    · simp [flatL_nil, Ssum]
  | cons h rest ih =>
    intro hlev hτ hβ s _ hs
    rw [List.pairwise_cons] at hlev
    have hsA : s ≤ Acnt L U h := hs h (by simp)
    have hdec := decomp U h L hL
    have hlen : Acnt L U h + Mcnt L U h ≤ L.length := by
      have := congrArg List.length hdec
      simp only [List.length_append] at this
      unfold Acnt Mcnt
      omega
    have hpre : ((L.map ρ).drop (Acnt L U h)).take (Mcnt L U h) =
        (L.filter (fun i => U i = h)).map ρ := by
      have e : L.map ρ = (L.filter (fun i => h < U i)).map ρ ++
          ((L.filter (fun i => U i = h)).map ρ ++ (L.filter (fun i => U i < h)).map ρ) := by
        conv_lhs => rw [← hdec]
        simp only [List.map_append]
      rw [e, List.drop_left' (l₁ := (L.filter (fun i => h < U i)).map ρ) (i := Acnt L U h)
          (by rw [List.length_map]; rfl),
        List.take_left' (l₁ := (L.filter (fun i => U i = h)).map ρ) (i := Mcnt L U h)
          (by rw [List.length_map]; rfl)]
    have hmono := drop_take_mono (L.map ρ) hρ (Mcnt L U h) s (Acnt L U h - s)
      (by rw [List.length_map]; omega)
    rw [show s + (Acnt L U h - s) = Acnt L U h by omega, hpre] at hmono
    obtain ⟨k, hk, hkm, hkτ⟩ := leastPrefix_le' ((L.map ρ).drop s) (τ h) (Mcnt L U h)
      (by rw [List.length_drop, List.length_map]; omega)
      ((hτ h (by simp)).trans hmono)
    have hs' : ∀ h' ∈ rest, s + k ≤ Acnt L U h' := by
      intro h' hh'
      have hlt : h' < h := hlev.1 h' hh'
      have := count_le (fun i => decide (h < U i)) (fun i => decide (U i = h))
        (fun i => decide (h' < U i))
        (fun x h1 h2 => by simp only [decide_eq_true_eq] at h1 h2; omega)
        (fun x hx => by simp only [decide_eq_true_eq] at hx ⊢; omega) L
      simp only [Acnt, Mcnt] at hlen hsA hkm ⊢
      omega
    obtain ⟨ks, hks, hl', hpt', hmem', hsum'⟩ :=
      ih hlev.2 (fun h' hh' => hτ h' (by simp [hh'])) (fun h' hh' => hβ h' (by simp [hh']))
        (s + k) (by simp only [Acnt, Mcnt] at hlen hsA hkm; omega) hs'
    have hkd : k ≤ ((L.map ρ).drop s).length := by
      rw [List.length_drop, List.length_map]
      omega
    refine ⟨k :: ks, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.map_cons, greedyLengths, hk, List.drop_drop, hks] <;> rfl
    · rw [flatL_cons, List.length_append, List.length_replicate]
      omega
    · intro t ht hst
      have hfl := flatL_cons h k rest ks
      have ht2 : t < (List.replicate k h ++ flatL rest ks).length := by rw [← hfl]; exact ht
      rw [List.getElem_of_eq hfl ht]
      by_cases htk : t < k
      · rw [List.getElem_append_left (by rw [List.length_replicate]; exact htk),
          List.getElem_replicate]
        apply pos_ge L U hL h (s + t) _ hst
        simp only [Acnt, Mcnt] at hsA hkm ⊢
        omega
      · have htk' : t - k < (flatL rest ks).length := by
          rw [List.length_append, List.length_replicate] at ht2
          omega
        rw [List.getElem_append_right (by rw [List.length_replicate]; omega)]
        have := hpt' (t - k) htk' (by omega)
        simp only [List.length_replicate, show s + t = s + k + (t - k) by omega]
        exact this
    · intro x hx
      rw [flatL_cons, List.mem_append] at hx
      rcases hx with hx | hx
      · rw [List.eq_of_mem_replicate hx]
        simp
      · exact List.mem_cons_of_mem _ (hmem' x hx)
    · rw [List.map_cons, List.sum_cons, flatL_cons, Ssum_app e _ h k _ hkd, List.drop_drop]
      have hnn : 0 ≤ (((L.map ρ).drop s).take k).sum := by
        refine List.sum_nonneg (fun x hx => ?_)
        obtain ⟨i, _, rfl⟩ := List.mem_map.1 (List.mem_of_mem_drop (List.mem_of_mem_take hx))
        exact hρ0 i
      have hb := hβ h (by simp) _ hnn hkτ
      linarith

lemma zip_le (f : Fin n → ℝ) (g : Fin n → ℕ → ℝ) : ∀ (l : List (Fin n)) (F : List ℕ),
    (∀ x ∈ l, 0 ≤ f x) → (∀ t (h1 : t < l.length) (h2 : t < F.length), g l[t] F[t] ≤ f l[t]) →
    (List.zipWith g l F).sum ≤ (l.map f).sum
  | [], F, _, _ => by simp
  | a :: l, [], hf, _ => by
    simp only [List.zipWith_nil_right, List.sum_nil, List.map_cons, List.sum_cons]
    have h1 : 0 ≤ (l.map f).sum := List.sum_nonneg (fun x hx => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      exact hf i (by simp [hi]))
    linarith [hf a (by simp)]
  | a :: l, ℓ :: F, hf, hg => by
    simp only [List.zipWith_cons_cons, List.sum_cons, List.map_cons]
    have h1 := hg 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at h1
    have h2 := zip_le f g l F (fun x hx => hf x (by simp [hx])) (fun t ht1 ht2 => by
      have := hg (t + 1) (by simp; omega) (by simp; omega)
      simpa using this)
    linarith

lemma chain_same (wt : Weights n) (hw : wt.Pos) (pM : ℕ →₀ ℝ) (hM : IsLaw pM)
    (W V : Fin n → ℕ) (hWV : W ≤ V) (j : Fin n) (hj : W j = V j) :
    expX wt pM V j ≤ expX wt pM W j := by
  unfold expX
  refine Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_left ?_ (hM.1 m))
  rw [expXm_eq, expXm_eq]
  refine ENNReal.toReal_mono (EX_ne_top _ hw W m j) ?_
  rw [EX_min wt hw V, EX_min wt hw W, hj]
  refine chain wt m _ W V (fun X k hX hXV hk => ?_) _ V hWV le_rfl rfl
  have hkj : k ≠ j := by
    intro h
    rw [h] at hk
    have h2 : X j ≤ V j := hXV j
    omega
  have := Rem_lem wt hw k m X _ 0 (adm_min k j hkj (V j)) (Or.inl rfl)
  rwa [fI0] at this

lemma relabel_ge (wt : Weights n) (hw : wt.Pos) (pM : ℕ →₀ ℝ) (hM : IsLaw pM)
    (I : Finset (Fin n)) (hI : wt.UniformOn I) (W V : Fin n → ℕ) (hWV : W ≤ V)
    (i j : Fin n) (hi : i ∈ I) (hj : j ∈ I) (hij : W i = V j) :
    expX wt pM V j ≤ expX wt pM W i := by
  by_cases hij' : i = j
  · rw [hij'] at hij ⊢
    exact chain_same wt hw pM hM W V hWV j hij
  have hτ : ∀ x, wt.w (Equiv.swap i j x) = wt.w x := by
    intro x
    by_cases hxi : x = i
    · rw [hxi, Equiv.swap_apply_left, hI i hi j hj]
    · by_cases hxj : x = j
      · rw [hxj, Equiv.swap_apply_right, hI i hi j hj]
      · rw [Equiv.swap_apply_of_ne_of_ne hxi hxj]
  have hperm := expX_perm wt hw (Equiv.swap i j) hτ pM W j
  rw [Equiv.swap_apply_right] at hperm
  rw [← hperm]
  have hle : W ∘ Equiv.swap i j ≤ V := by
    refine Pi.le_def.2 (fun x => ?_)
    simp only [Function.comp_apply]
    by_cases hxi : x = i
    · rw [hxi, Equiv.swap_apply_left]
      have h1 : W j ≤ V j := hWV j
      have h2 : W i ≤ V i := hWV i
      omega
    · by_cases hxj : x = j
      · rw [hxj, Equiv.swap_apply_right, hij]
      · rw [Equiv.swap_apply_of_ne_of_ne hxi hxj]
        exact hWV x
  refine chain_same wt hw pM hM _ V hle j ?_
  simp only [Function.comp_apply, Equiv.swap_apply_right]
  exact hij

end Aux_MNLS0

set_option maxHeartbeats 1600000 in
open MNLStability Aux_MNLS0 in
theorem solution {n : ℕ} (hn : 1 ≤ n) (wts : Weights n) (hw : wts.Pos) (r : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ r i)
    (pM : ℕ →₀ ℝ) (hM : IsLaw pM) (I : Finset (Fin n)) (hI : wts.UniformOn I)
    (ord : List (Fin n)) (hord : IsPriceOrder r I ord) (C : ℕ) (ε : ℝ) (hε : 0 < ε)
    (H : Finset ℕ) (hH : IsSpaced ε C H) (U : Fin n → ℕ) (hU : norm1 U ≤ C)
    (Ustep : Fin n → ℕ) (hoff : ∀ i, i ∉ I → Ustep i = U i) (hval : ∀ i ∈ I, Ustep i ∈ H)
    (hmono : NonincAlong ord Ustep)
    (h1 : ∀ i, i ∉ I → expX wts pM U i ≤ expX wts pM Ustep i)
    (h2 : (1 - ε) * ∑ i ∈ I, r i * expX wts pM U i ≤ ∑ i ∈ I, r i * expX wts pM Ustep i)
    (h3 : norm1 Ustep ≤ norm1 U)
    (hpos : ∃ h ∈ H, 0 < Rlev wts r pM I Ustep h)
    (R0 : ℝ) (Rt Et : ℕ → ℝ)
    (hR0 : (1 - ε) * ∑ h ∈ Lam wts r pM I H Ustep ε, Rlev wts r pM I Ustep h ≤ R0 ∧
      R0 ≤ ∑ h ∈ Lam wts r pM I H Ustep ε, Rlev wts r pM I Ustep h)
    (hRt : ∀ h ∈ Lam wts r pM I H Ustep ε,
      Rlev wts r pM I Ustep h - ε / H.card * R0 ≤ Rt h ∧ Rt h ≤ Rlev wts r pM I Ustep h)
    (hEt : ∀ h ∈ Lam wts r pM I H Ustep ε, ∀ i ∈ lev I Ustep h,
      expX wts pM Ustep i ≤ Et h ∧ Et h ≤ (1 + ε) * expX wts pM Ustep i) :
    ∃ ks : List ℕ,
      greedyLengths (ord.map r) ((lamList wts r pM I H Ustep ε).map fun h => Rt h / Et h) =
        some ks ∧
      (∀ i, i ∉ I →
        expX wts pM U i ≤ expX wts pM (swap I U (stepVec ord (lamList wts r pM I H Ustep ε) ks)) i) ∧
      (1 - 3 * ε) * ∑ i ∈ I, r i * expX wts pM U i ≤
        ∑ i ∈ I, r i * expX wts pM (swap I U (stepVec ord (lamList wts r pM I H Ustep ε) ks)) i ∧
      norm1 (swap I U (stepVec ord (lamList wts r pM I H Ustep ε) ks)) ≤ norm1 U := by
  obtain ⟨hnd, hmem, hpr⟩ := hord
  obtain ⟨hmH, hRmin⟩ := hMin_facts wts r pM I H Ustep hpos
  obtain ⟨hm, hhm⟩ : ∃ hm, hm = hMin wts r pM I H Ustep := ⟨_, rfl⟩
  rw [← hhm] at hmH hRmin
  have hlevI : ∀ h i, i ∈ lev I Ustep h → i ∈ I ∧ Ustep i = h := fun h i hi =>
    Finset.mem_filter.1 hi
  have hX : ∀ (W : Fin n → ℕ) i, 0 ≤ expX wts pM W i := fun W i => expX_nonneg wts pM hM W i
  have hHc : (0 : ℝ) < H.card := Nat.cast_pos.2 (Finset.card_pos.2 ⟨0, hH.1⟩)
  have hRnn : ∀ h, 0 ≤ Rlev wts r pM I Ustep h := fun h =>
    Finset.sum_nonneg (fun j _ => mul_nonneg (hr j) (hX _ j))
  have hlam : ∀ h ∈ Lam wts r pM I H Ustep ε, 0 < Rlev wts r pM I Ustep h := by
    intro h hh
    have h1 := Finset.mem_filter.1 hh
    rw [← hhm] at h1
    have := mul_pos (div_pos hε hHc) hRmin
    linarith [h1.2]
  have hlevne : ∀ h ∈ Lam wts r pM I H Ustep ε, (lev I Ustep h).Nonempty := by
    intro h hh
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have := hlam h hh
    unfold Rlev at this
    rw [he, Finset.sum_empty] at this
    exact lt_irrefl _ this
  have hsame : ∀ i j, i ∈ I → j ∈ I → Ustep i = Ustep j →
      expX wts pM Ustep i = expX wts pM Ustep j := by
    intro i j hi hj hij
    exact le_antisymm (sales_expX wts hw pM hM j i (hI j hj i hi) Ustep hij.le)
      (sales_expX wts hw pM hM i j (hI i hi j hj) Ustep hij.ge)
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℝ, e = fun ℓ =>
      if hne : (lev I Ustep ℓ).Nonempty then expX wts pM Ustep hne.choose else 0 := ⟨_, rfl⟩
  have he_eq : ∀ ℓ j, j ∈ lev I Ustep ℓ → e ℓ = expX wts pM Ustep j := by
    intro ℓ j hj
    have hne : (lev I Ustep ℓ).Nonempty := ⟨j, hj⟩
    rw [he]
    simp only [dif_pos hne]
    obtain ⟨hcI, hcU⟩ := hlevI _ _ hne.choose_spec
    obtain ⟨hjI, hjU⟩ := hlevI _ _ hj
    exact hsame _ _ hcI hjI (hcU.trans hjU.symm)
  have hmemlam : ∀ h, h ∈ lamList wts r pM I H Ustep ε ↔ h ∈ Lam wts r pM I H Ustep ε := by
    intro h
    unfold lamList
    rw [List.mem_reverse, Finset.mem_sort]
  have hτ : ∀ h ∈ lamList wts r pM I H Ustep ε,
      Rt h / Et h ≤ ((ord.filter (fun i => Ustep i = h)).map r).sum := by
    intro h hh
    rw [hmemlam] at hh
    have hlv : lev I Ustep h = (ord.filter (fun i => Ustep i = h)).toFinset := by
      ext i
      simp only [lev, Finset.mem_filter, List.mem_toFinset, List.mem_filter, decide_eq_true_eq,
        hmem i]
    have hsl : ∑ i ∈ lev I Ustep h, r i = ((ord.filter (fun i => Ustep i = h)).map r).sum := by
      rw [hlv, List.sum_toFinset _ (hnd.filter _)]
    rw [← hsl]
    obtain ⟨i0, hi0⟩ := hlevne h hh
    have hEt0 : 0 ≤ Et h := (hX _ i0).trans (hEt h hh i0 hi0).1
    rcases eq_or_lt_of_le hEt0 with h0 | hEp
    · rw [← h0, div_zero]
      exact Finset.sum_nonneg (fun i _ => hr i)
    · rw [div_le_iff₀ hEp]
      calc Rt h ≤ Rlev wts r pM I Ustep h := (hRt h hh).2
        _ = ∑ i ∈ lev I Ustep h, r i * expX wts pM Ustep i := rfl
        _ ≤ ∑ i ∈ lev I Ustep h, r i * Et h :=
            Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hEt h hh i hi).1 (hr i))
        _ = (∑ i ∈ lev I Ustep h, r i) * Et h := by rw [Finset.sum_mul]
  have hβ : ∀ h ∈ lamList wts r pM I H Ustep ε, ∀ x : ℝ, 0 ≤ x → Rt h / Et h ≤ x →
      Rt h / (1 + ε) ≤ e h * x := by
    intro h hh x hx0 hx
    rw [hmemlam] at hh
    obtain ⟨j, hj⟩ := hlevne h hh
    rw [he_eq h j hj]
    have hE := hEt h hh j hj
    have hEpos : 0 < expX wts pM Ustep j := by
      by_contra h0
      push_neg at h0
      have hz : Rlev wts r pM I Ustep h = 0 := by
        refine Finset.sum_eq_zero (fun j' hj' => ?_)
        rw [← he_eq h j' hj', he_eq h j hj, le_antisymm h0 (hX _ j), mul_zero]
      linarith [hlam h hh]
    have hEt0 : 0 < Et h := lt_of_lt_of_le hEpos hE.1
    rcases le_or_gt 0 (Rt h) with hR | hR
    · have k1 : 1 / (1 + ε) ≤ expX wts pM Ustep j / Et h := by
        rw [div_le_div_iff₀ (by linarith) hEt0]
        linarith [hE.2]
      calc Rt h / (1 + ε) = Rt h * (1 / (1 + ε)) := by ring
        _ ≤ Rt h * (expX wts pM Ustep j / Et h) := mul_le_mul_of_nonneg_left k1 hR
        _ = expX wts pM Ustep j * (Rt h / Et h) := by ring
        _ ≤ expX wts pM Ustep j * x := mul_le_mul_of_nonneg_left hx (hX _ j)
    · have : Rt h / (1 + ε) ≤ 0 := by
        rw [div_le_iff₀ (by linarith)]
        linarith
      exact this.trans (mul_nonneg (hX _ j) hx0)
  have hsorted : (lamList wts r pM I H Ustep ε).Pairwise (fun a b => b < a) := by
    unfold lamList
    rw [List.pairwise_reverse]
    have h1 : ((Lam wts r pM I H Ustep ε).sort (· ≤ ·)).Pairwise (· ≤ ·) :=
      Finset.pairwise_sort _ _
    have h2 : ((Lam wts r pM I H Ustep ε).sort (· ≤ ·)).Nodup := Finset.sort_nodup _ _
    exact (h1.and h2).imp (fun h => lt_of_le_of_ne h.1 h.2)
  obtain ⟨ks, hks, hlen, hpt, hmemF, hsum⟩ := greedy9 ord Ustep r (fun h => Rt h / Et h) e
    (fun h => Rt h / (1 + ε)) hmono (List.pairwise_map.2 hpr) hr
    (lamList wts r pM I H Ustep ε) hsorted hτ hβ 0 (Nat.zero_le _) (fun _ _ => Nat.zero_le _)
  rw [List.drop_zero] at hks hsum
  refine ⟨ks, hks, ?_⟩
  obtain ⟨F, hF⟩ : ∃ F, F = flatL (lamList wts r pM I H Ustep ε) ks := ⟨_, rfl⟩
  rw [← hF] at hlen hpt hmemF hsum
  obtain ⟨V', hV'⟩ : ∃ V', V' = stepVec ord (lamList wts r pM I H Ustep ε) ks := ⟨_, rfl⟩
  obtain ⟨U', hU'⟩ : ∃ U', U' = swap I U V' := ⟨_, rfl⟩
  rw [← hV', ← hU']
  have hV't : ∀ t (ht : t < ord.length), V' ord[t] = F.getD t 0 := by
    intro t ht
    rw [hV', hF]
    unfold stepVec
    rw [if_pos (List.getElem_mem ht), hnd.idxOf_getElem t ht]
    rfl
  have hU'I : ∀ i ∈ I, U' i = V' i := by
    intro i hi
    rw [hU']
    simp only [swap, if_pos hi]
  have hU'off : ∀ i, i ∉ I → U' i = Ustep i := by
    intro i hi
    rw [hU']
    simp only [swap, if_neg hi]
    exact (hoff i hi).symm
  have hU't : ∀ t (ht : t < ord.length), U' ord[t] = F.getD t 0 := by
    intro t ht
    rw [hU'I _ ((hmem _).1 (List.getElem_mem ht)), hV't t ht]
  have hle : U' ≤ Ustep := by
    refine Pi.le_def.2 (fun i => ?_)
    by_cases hi : i ∈ I
    · obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem ((hmem i).2 hi)
      rw [hU't t ht]
      by_cases htF : t < F.length
      · rw [List.getD_eq_getElem _ _ htF]
        have := hpt t htF (by omega)
        simp only [zero_add] at this
        exact this
      · rw [List.getD_eq_default _ _ (by omega)]
        exact Nat.zero_le _
    · rw [hU'off i hi]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact (h1 i hi).trans (chain_same wts hw pM hM U' Ustep hle i (hU'off i hi))
  · -- revenue
    have hI' : ord.toFinset = I := by
      ext i
      simp [hmem i]
    have hrevU' : ∑ i ∈ I, r i * expX wts pM U' i = (ord.map (fun i => r i * expX wts pM U' i)).sum := by
      rw [← hI', List.sum_toFinset _ hnd]
    have hS : Ssum e (ord.map r) F ≤ ∑ i ∈ I, r i * expX wts pM U' i := by
      rw [hrevU']
      unfold Ssum
      rw [List.zipWith_map_left]
      refine zip_le _ (fun i ℓ => r i * e ℓ) ord F
        (fun x _ => mul_nonneg (hr x) (hX _ x)) (fun t ht1 ht2 => ?_)
      have hFt : F[t] ∈ Lam wts r pM I H Ustep ε :=
        (hmemlam _).1 (hmemF _ (List.getElem_mem ht2))
      obtain ⟨j, hj⟩ := hlevne _ hFt
      obtain ⟨hjI, hjU⟩ := hlevI _ _ hj
      show r ord[t] * e F[t] ≤ r ord[t] * expX wts pM U' ord[t]
      rw [he_eq _ j hj]
      refine mul_le_mul_of_nonneg_left ?_ (hr _)
      refine relabel_ge wts hw pM hM I hI U' Ustep hle ord[t] j
        ((hmem _).1 (List.getElem_mem ht1)) hjI ?_
      rw [hU't t ht1, List.getD_eq_getElem _ _ ht2, hjU]
    have hlamsum : ((lamList wts r pM I H Ustep ε).map (fun h => Rt h / (1 + ε))).sum =
        (∑ h ∈ Lam wts r pM I H Ustep ε, Rt h) / (1 + ε) := by
      have hnd' : (lamList wts r pM I H Ustep ε).Nodup := by
        unfold lamList
        exact List.nodup_reverse.2 (Finset.sort_nodup _ _)
      have htf : (lamList wts r pM I H Ustep ε).toFinset = Lam wts r pM I H Ustep ε := by
        ext h
        rw [List.mem_toFinset, hmemlam]
      rw [← List.sum_toFinset _ hnd', htf, Finset.sum_div]
    -- bookkeeping of the levels
    obtain ⟨SΛ, hSΛ⟩ : ∃ S, S = ∑ h ∈ Lam wts r pM I H Ustep ε, Rlev wts r pM I Ustep h :=
      ⟨_, rfl⟩
    obtain ⟨SH, hSH⟩ : ∃ S, S = ∑ i ∈ I, r i * expX wts pM Ustep i := ⟨_, rfl⟩
    have hLamH : Lam wts r pM I H Ustep ε ⊆ H := Finset.filter_subset _ _
    have hpart : ∑ h ∈ H, Rlev wts r pM I Ustep h = SH := by
      rw [hSH]
      show ∑ h ∈ H, ∑ i ∈ lev I Ustep h, r i * expX wts pM Ustep i = _
      exact Finset.sum_fiberwise_of_maps_to (f := fun i => r i * expX wts pM Ustep i) hval
    have hsplit := Finset.sum_sdiff hLamH (f := fun h => Rlev wts r pM I Ustep h)
    have hout : ∑ h ∈ H \ Lam wts r pM I H Ustep ε, Rlev wts r pM I Ustep h ≤
        ((H \ Lam wts r pM I H Ustep ε).card : ℝ) *
          (ε / H.card * Rlev wts r pM I Ustep hm) := by
      have := Finset.sum_le_card_nsmul (H \ Lam wts r pM I H Ustep ε)
        (fun h => Rlev wts r pM I Ustep h) (ε / H.card * Rlev wts r pM I Ustep hm)
        (fun h hh => by
          rw [Finset.mem_sdiff] at hh
          have hnot : ¬ (ε / H.card * Rlev wts r pM I Ustep (hMin wts r pM I H Ustep) ≤
              Rlev wts r pM I Ustep h) := fun hc => hh.2 (Finset.mem_filter.2 ⟨hh.1, hc⟩)
          rw [← hhm] at hnot
          push_neg at hnot
          exact hnot.le)
      simpa [nsmul_eq_mul] using this
    have hRmSH : Rlev wts r pM I Ustep hm ≤ SH := by
      rw [← hpart]
      exact Finset.single_le_sum (f := fun h => Rlev wts r pM I Ustep h)
        (fun h _ => hRnn h) hmH
    have hRtsum : SΛ - ((Lam wts r pM I H Ustep ε).card : ℝ) * (ε / H.card * R0) ≤
        ∑ h ∈ Lam wts r pM I H Ustep ε, Rt h := by
      rw [hSΛ]
      have := Finset.sum_le_sum (fun h hh => (hRt h hh).1)
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at this
      linarith
    have hcardsum : ((Lam wts r pM I H Ustep ε).card : ℝ) +
        ((H \ Lam wts r pM I H Ustep ε).card : ℝ) = H.card := by
      rw [Finset.card_sdiff_of_subset hLamH]
      have := Finset.card_le_card hLamH
      push_cast [this]
      ring
    obtain ⟨x, hx⟩ : ∃ x : ℝ, x = ((Lam wts r pM I H Ustep ε).card : ℝ) * ε / H.card := ⟨_, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y : ℝ, y = ((H \ Lam wts r pM I H Ustep ε).card : ℝ) * ε / H.card :=
      ⟨_, rfl⟩
    have hxy : x + y = ε := by
      rw [hx, hy, ← add_div, ← add_mul, hcardsum, mul_div_cancel_left₀ _ hHc.ne']
    have hx0 : 0 ≤ x := by rw [hx]; exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hε.le) hHc.le
    have hy0 : 0 ≤ y := by rw [hy]; exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hε.le) hHc.le
    have hU'sum := hS
    have hRU0 : 0 ≤ ∑ i ∈ I, r i * expX wts pM U i :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hr i) (hX _ i))
    have hRU'0 : 0 ≤ ∑ i ∈ I, r i * expX wts pM U' i :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hr i) (hX _ i))
    by_cases hε3 : 1 / 3 ≤ ε
    · have := mul_nonneg (sub_nonneg.2 hε3) hRU0
      nlinarith
    push_neg at hε3
    have k0 : (∑ h ∈ Lam wts r pM I H Ustep ε, Rt h) / (1 + ε) ≤
        ∑ i ∈ I, r i * expX wts pM U' i := by
      rw [← hlamsum]
      exact hsum.trans hS
    have k1 : SΛ - x * SΛ ≤ (1 + ε) * ∑ i ∈ I, r i * expX wts pM U' i := by
      rw [div_le_iff₀ (by linarith)] at k0
      have e1 : ((Lam wts r pM I H Ustep ε).card : ℝ) * (ε / H.card * R0) = x * R0 := by
        rw [hx]; ring
      rw [e1] at hRtsum
      have hR0le : R0 ≤ SΛ := by rw [hSΛ]; exact hR0.2
      have := mul_le_mul_of_nonneg_left hR0le hx0
      linarith
    have k2 : (1 - y) * SH ≤ SΛ := by
      have e2 : ((H \ Lam wts r pM I H Ustep ε).card : ℝ) *
          (ε / H.card * Rlev wts r pM I Ustep hm) = y * Rlev wts r pM I Ustep hm := by
        rw [hy]; ring
      rw [e2] at hout
      have := mul_le_mul_of_nonneg_left hRmSH hy0
      have hsp : ∑ h ∈ H \ Lam wts r pM I H Ustep ε, Rlev wts r pM I Ustep h + SΛ = SH := by
        rw [hSΛ, ← hpart]
        exact hsplit
      linarith
    have hSH0 : 0 ≤ SH := by rw [← hpart]; exact Finset.sum_nonneg (fun h _ => hRnn h)
    have hx1 : 0 ≤ 1 - x := by linarith
    have k3 : (1 - x) * ((1 - y) * SH) ≤ (1 - x) * SΛ := mul_le_mul_of_nonneg_left k2 hx1
    have k4 : (1 - ε) * SH ≤ (1 - x) * ((1 - y) * SH) := by
      have h4 : (1 - ε) ≤ (1 - x) * (1 - y) := by nlinarith [mul_nonneg hx0 hy0]
      have h4' := mul_le_mul_of_nonneg_right h4 hSH0
      calc (1 - ε) * SH ≤ (1 - x) * (1 - y) * SH := h4'
        _ = (1 - x) * ((1 - y) * SH) := by ring
    have k5 : (1 - ε) * ((1 - ε) * ∑ i ∈ I, r i * expX wts pM U i) ≤ (1 - ε) * SH := by
      rw [hSH]
      exact mul_le_mul_of_nonneg_left h2 (by linarith)
    have k6 : (1 - 3 * ε) * (1 + ε) ≤ (1 - ε) * (1 - ε) := by nlinarith [sq_nonneg ε]
    have k6' := mul_le_mul_of_nonneg_right k6 hRU0
    have k7 : (1 + ε) * ((1 - 3 * ε) * ∑ i ∈ I, r i * expX wts pM U i) ≤
        (1 + ε) * ∑ i ∈ I, r i * expX wts pM U' i := by
      calc (1 + ε) * ((1 - 3 * ε) * ∑ i ∈ I, r i * expX wts pM U i)
          = (1 - 3 * ε) * (1 + ε) * ∑ i ∈ I, r i * expX wts pM U i := by ring
        _ ≤ (1 - ε) * (1 - ε) * ∑ i ∈ I, r i * expX wts pM U i := k6'
        _ = (1 - ε) * ((1 - ε) * ∑ i ∈ I, r i * expX wts pM U i) := by ring
        _ ≤ (1 - ε) * SH := k5
        _ ≤ (1 - x) * ((1 - y) * SH) := k4
        _ ≤ (1 - x) * SΛ := k3
        _ = SΛ - x * SΛ := by ring
        _ ≤ (1 + ε) * ∑ i ∈ I, r i * expX wts pM U' i := k1
    exact le_of_mul_le_mul_left k7 (by linarith)
  · calc norm1 U' ≤ norm1 Ustep := Finset.sum_le_sum (fun i _ => hle i)
      _ ≤ norm1 U := h3
