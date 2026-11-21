-- Prove2me | solution 1 for MNLStability.evaluation_oracle
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T03:51:41.904231+00:00
-- url     : https://prove2.me/submissions/3b9637f3-b2c8-42df-b9d6-3bdaffe25581

import Mathlib
import Definitions.Def_MNLStability_IsLaw
import Definitions.Def_MNLStability_expX
import Definitions.Def_MNLStability_opt
import Definitions.Def_MNLStability_estimate

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


lemma EEx_const' {α : Type*} (μ : PMF α) (c : ℝ≥0∞) : EEx μ (fun _ => c) = c := by
  unfold EEx
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

lemma Xf_shf (i : Fin n) (c : Option (Fin n)) :
    (Xf i ∘ shf c) = fun x => Xf i x + (if c = some i then 1 else 0) := by
  funext x
  rcases c with _ | j
  · simp [Xf, shf]
  · by_cases hj : j = i
    · subst hj
      simp [Xf, shf]
    · simp [Xf, shf, Pi.single_apply, hj, Ne.symm hj]

lemma sb1_apply (V : Fin n → ℕ) (i : Fin n) (c : Option (Fin n)) :
    (sb1 V c) i = V i - (if c = some i then 1 else 0) := by
  rcases c with _ | j
  · simp [sb1]
  · by_cases hj : j = i
    · subst hj
      simp [sb1]
    · simp [sb1, Pi.single_apply, hj, Ne.symm hj]

lemma q_eq (wt : Weights n) (hw : wt.Pos) (V : Fin n → ℕ) (c : Option (Fin n)) :
    (step wt V c).toReal = qq wt V c / ∑ d, qq wt V d := by
  rw [step_eq wt hw, ENNReal.toReal_ofReal (div_nonneg (qq_nonneg wt hw V c) (Z_pos wt hw V).le)]

lemma q_sum (wt : Weights n) (V : Fin n → ℕ) : ∑ c, (step wt V c).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun c _ => PMF.apply_ne_top _ _), step_sum_one]
  simp

lemma Wtot_ge (wt : Weights n) (hw : wt.Pos) (V : Fin n → ℕ) :
    wt.wsum (inStock V) ≤ ∑ j, wt.w j := by
  unfold Weights.wsum
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun j _ _ => (hw.2 j).le)

lemma wsum_nonneg (wt : Weights n) (hw : wt.Pos) (V : Fin n → ℕ) : 0 ≤ wt.wsum (inStock V) :=
  Finset.sum_nonneg (fun j _ => (hw.2 j).le)

lemma q_some (wt : Weights n) (hw : wt.Pos) (V : Fin n → ℕ) (i : Fin n) (hV : 0 < V i) :
    (step wt V (some i)).toReal = wt.w i / (wt.w0 + wt.wsum (inStock V)) := by
  rw [q_eq wt hw, ZZ_eq]
  simp [qq, hV]

lemma q_some_zero (wt : Weights n) (hw : wt.Pos) (V : Fin n → ℕ) (i : Fin n) (hV : V i = 0) :
    (step wt V (some i)).toReal = 0 := by
  rw [q_eq wt hw]
  simp [qq, hV]

lemma le_wmax (wt : Weights n) (j : Fin n) : wt.w j ≤ wt.wmax := by
  unfold Weights.wmax
  have key : ∀ l : List ℝ, ∀ x ∈ l, x ≤ l.foldr max 0 := by
    intro l
    induction l with
    | nil => intro x hx; simp at hx
    | cons a l ih =>
      intro x hx
      rw [List.foldr_cons]
      rcases List.mem_cons.1 hx with h | h
      · rw [h]; exact le_max_left _ _
      · exact (ih x h).trans (le_max_right _ _)
  exact key _ _ (List.mem_map.2 ⟨j, List.mem_finRange j, rfl⟩)

lemma sum_sort_eq (pM : ℕ →₀ ℝ) (f : ℕ → ℕ) :
    ((pM.support.sort (· ≤ ·)).map f).sum = ∑ m ∈ pM.support, f m := by
  rw [← List.sum_toFinset f (Finset.sort_nodup _ _), Finset.sort_toFinset]



/-! ## Programs that never read their cost counter -/

def Obl {α : Type} (p : Prog α) : Prop :=
  ∀ s, p.run s = (p.run 0).map (fun x => (x.1, x.2 + s))

noncomputable def vl {α : Type} (p : Prog α) : PMF α := (p.run 0).map Prod.fst

lemma run_bind' {α β : Type} (p : Prog α) (f : α → Prog β) (s : ℕ) :
    (p >>= f).run s = (p.run s).bind (fun x => (f x.1).run x.2) := rfl

lemma Obl_pure {α : Type} (a : α) : Obl (pure a : Prog α) := by
  intro s
  show PMF.pure (a, s) = (PMF.pure (a, 0)).map _
  rw [PMF.pure_map, Nat.zero_add]

lemma Obl_charge (k : ℕ) : Obl (charge k) := by
  intro s
  show PMF.pure ((), s + k) = (PMF.pure ((), 0 + k)).map _
  rw [PMF.pure_map, Nat.zero_add, Nat.add_comm]

lemma Obl_lift {α : Type} (μ : PMF α) : Obl (StateT.lift μ : Prog α) := by
  intro s
  show μ.bind (fun a => PMF.pure (a, s)) = (μ.bind (fun a => PMF.pure (a, 0))).map _
  rw [PMF.map_bind]
  congr 1
  funext a
  rw [PMF.pure_map, Nat.zero_add]

lemma Obl_bind {α β : Type} {p : Prog α} {f : α → Prog β} (hp : Obl p) (hf : ∀ a, Obl (f a)) :
    Obl (p >>= f) := by
  intro s
  rw [run_bind', run_bind', hp s, PMF.bind_map, PMF.map_bind]
  congr 1
  funext x
  simp only [Function.comp_apply]
  rw [hf x.1 (x.2 + s), hf x.1 x.2, PMF.map_comp]
  congr 1
  funext y
  simp only [Function.comp_apply, Nat.add_assoc]

lemma Obl_opn {α : Type} (k : ℕ) (a : α) : Obl (opn k a) := by
  unfold opn
  exact Obl_bind (Obl_charge k) (fun _ => Obl_pure a)

lemma Obl_ite {α : Type} (c : Prop) [Decidable c] {p q : Prog α} (hp : Obl p) (hq : Obl q) :
    Obl (if c then p else q) := by
  split_ifs
  · exact hp
  · exact hq

lemma Obl_foldP {α β : Type} (f : β → α → Prog β) (hf : ∀ b a, Obl (f b a)) :
    ∀ (l : List α) (b : β), Obl (foldP l f b)
  | [], b => Obl_pure b
  | a :: l, b => by
    show Obl (charge 1 >>= fun _ => (f b a >>= fun b' => foldP l f b'))
    exact Obl_bind (Obl_charge 1) (fun _ => Obl_bind (hf b a) (fun b' => Obl_foldP f hf l b'))

lemma vl_bind {α β : Type} {p : Prog α} {f : α → Prog β} (hp : Obl p) (hf : ∀ a, Obl (f a)) :
    vl (p >>= f) = (vl p).bind (fun a => vl (f a)) := by
  unfold vl
  rw [run_bind', PMF.map_bind, PMF.bind_map]
  congr 1
  funext x
  simp only [Function.comp_apply]
  rw [hf x.1 x.2, PMF.map_comp]
  rfl

lemma vl_pure {α : Type} (a : α) : vl (pure a : Prog α) = PMF.pure a := by
  unfold vl
  show (PMF.pure (a, 0)).map Prod.fst = _
  rw [PMF.pure_map]

lemma vl_charge (k : ℕ) : vl (charge k) = PMF.pure () := by
  unfold vl
  show (PMF.pure ((), 0 + k)).map Prod.fst = _
  rw [PMF.pure_map]

lemma vl_opn {α : Type} (k : ℕ) (a : α) : vl (opn k a) = PMF.pure a := by
  unfold opn
  rw [vl_bind (Obl_charge k) (fun _ => Obl_pure a), vl_charge, PMF.pure_bind, vl_pure]

lemma vl_lift {α : Type} (μ : PMF α) : vl (StateT.lift μ : Prog α) = μ := by
  unfold vl
  show (μ.bind (fun a => PMF.pure (a, 0))).map Prod.fst = μ
  rw [PMF.map_bind]
  conv_rhs => rw [← PMF.bind_pure μ]
  congr 1
  funext a
  rw [PMF.pure_map]

lemma vl_ite {α : Type} (c : Prop) [Decidable c] (p q : Prog α) :
    vl (if c then p else q) = if c then vl p else vl q := by
  split_ifs <;> rfl

/-! ## Cost bounds over all runs -/

def CostLe {α : Type} (p : Prog α) (K : ℕ) : Prop := ∀ x ∈ (p.run 0).support, x.2 ≤ K

lemma Obl_support {α : Type} {p : Prog α} (hp : Obl p) (s : ℕ) (x : α × ℕ)
    (hx : x ∈ (p.run s).support) : ∃ y ∈ (p.run 0).support, x = (y.1, y.2 + s) := by
  rw [hp s, PMF.mem_support_map_iff] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, hy, rfl⟩

lemma CostLe_bind {α β : Type} {p : Prog α} {f : α → Prog β} {K K' : ℕ} (hp : CostLe p K)
    (hfo : ∀ a, Obl (f a)) (hf : ∀ a, CostLe (f a) K') : CostLe (p >>= f) (K + K') := by
  intro x hx
  rw [run_bind', PMF.mem_support_bind_iff] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  obtain ⟨z, hz, rfl⟩ := Obl_support (hfo y.1) y.2 x hxy
  have h1 := hp y hy
  have h2 := hf y.1 z hz
  show z.2 + y.2 ≤ K + K'
  omega

lemma CostLe_mono {α : Type} {p : Prog α} {K K' : ℕ} (h : CostLe p K) (hK : K ≤ K') :
    CostLe p K' := fun x hx => (h x hx).trans hK

lemma CostLe_pure {α : Type} (a : α) : CostLe (pure a : Prog α) 0 := by
  intro x hx
  have : x = (a, 0) := by
    have hx' : x ∈ (PMF.pure (a, 0)).support := hx
    rwa [PMF.mem_support_pure_iff] at hx'
  rw [this]

lemma CostLe_charge (k : ℕ) : CostLe (charge k) k := by
  intro x hx
  have : x = ((), 0 + k) := by
    have hx' : x ∈ (PMF.pure ((), 0 + k)).support := hx
    rwa [PMF.mem_support_pure_iff] at hx'
  rw [this]
  simp

lemma CostLe_opn {α : Type} (k : ℕ) (a : α) : CostLe (opn k a) k := by
  unfold opn
  exact CostLe_mono (CostLe_bind (CostLe_charge k) (fun _ => Obl_pure a) (fun _ => CostLe_pure a))
    (by simp)

lemma CostLe_lift {α : Type} (μ : PMF α) : CostLe (StateT.lift μ : Prog α) 0 := by
  intro x hx
  have hx' : x ∈ (μ.bind (fun a => PMF.pure (a, 0))).support := hx
  rw [PMF.mem_support_bind_iff] at hx'
  obtain ⟨a, _, ha⟩ := hx'
  rw [PMF.mem_support_pure_iff] at ha
  rw [ha]

lemma CostLe_ite {α : Type} (c : Prop) [Decidable c] {p q : Prog α} {K : ℕ} (hp : CostLe p K)
    (hq : CostLe q K) : CostLe (if c then p else q) K := by
  split_ifs
  · exact hp
  · exact hq

lemma CostLe_foldP {α β : Type} (f : β → α → Prog β) (hfo : ∀ b a, Obl (f b a)) (K : ℕ)
    (hf : ∀ b a, CostLe (f b a) K) :
    ∀ (l : List α) (b : β), CostLe (foldP l f b) (l.length * (K + 1))
  | [], b => by
    simp only [List.length_nil, Nat.zero_mul]
    exact CostLe_pure b
  | a :: l, b => by
    show CostLe (charge 1 >>= fun _ => (f b a >>= fun b' => foldP l f b')) _
    refine CostLe_mono (CostLe_bind (CostLe_charge 1)
      (fun _ => Obl_bind (hfo b a) (fun b' => Obl_foldP f hfo l b'))
      (fun _ => CostLe_bind (hf b a) (fun b' => Obl_foldP f hfo l b')
        (fun b' => CostLe_foldP f hfo K hf l b'))) ?_
    simp only [List.length_cons]
    nlinarith


/-! ## Geometric and categorical draws -/

lemma geom_tsum (g : ℝ) (hg0 : 0 < g) (hg1 : g ≤ 1) :
    ∑' k, ENNReal.ofReal ((1 - g) ^ k * g) = 1 := by
  have h0 : 0 ≤ 1 - g := by linarith
  have h1 : 1 - g < 1 := by linarith
  have hs : Summable (fun k : ℕ => (1 - g) ^ k * g) :=
    (summable_geometric_of_lt_one h0 h1).mul_right g
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (pow_nonneg h0 k) hg0.le) hs,
    tsum_mul_right, tsum_geometric_of_lt_one h0 h1]
  rw [show (1 - (1 - g)) = g by ring, inv_mul_cancel₀ hg0.ne', ENNReal.ofReal_one]

lemma geomPMF_apply (g : ℝ) (hg0 : 0 < g) (hg1 : g ≤ 1) (k : ℕ) :
    geomPMF g k = ENNReal.ofReal ((1 - g) ^ k * g) := by
  have h := geom_tsum g hg0 hg1
  have e : geomPMF g = ⟨fun k => ENNReal.ofReal ((1 - g) ^ k * g), h ▸ ENNReal.summable.hasSum⟩ :=
    dif_pos h
  rw [e]
  rfl

lemma sum_range_getD : ∀ p : List ℝ, ∑ k ∈ Finset.range p.length, p.getD k 0 = p.sum
  | [] => by simp
  | a :: p => by
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [sum_range_getD p, add_comm]

lemma cat_tsum (p : List ℝ) (hp : ∀ x ∈ p, 0 ≤ x) (hs : p.sum = 1) :
    ∑' k, ENNReal.ofReal (p.getD k 0) = 1 := by
  rw [tsum_eq_sum (s := Finset.range p.length)]
  · rw [← ENNReal.ofReal_sum_of_nonneg]
    · rw [sum_range_getD p, hs, ENNReal.ofReal_one]
    · intro k hk
      rw [Finset.mem_range] at hk
      rw [List.getD_eq_getElem _ _ hk]
      exact hp _ (List.getElem_mem hk)
  · intro k hk
    rw [Finset.mem_range, not_lt] at hk
    rw [List.getD_eq_default _ _ hk, ENNReal.ofReal_zero]

lemma catPMF_apply (p : List ℝ) (hp : ∀ x ∈ p, 0 ≤ x) (hs : p.sum = 1) (k : ℕ) :
    catPMF p k = ENNReal.ofReal (p.getD k 0) := by
  have h := cat_tsum p hp hs
  have e : catPMF p = ⟨fun k => ENNReal.ofReal (p.getD k 0), h ▸ ENNReal.summable.hasSum⟩ :=
    dif_pos h
  rw [e]
  rfl

/-! ## Expected revenue of the demand process -/

noncomputable def Fr (wt : Weights n) (r : Fin n → ℝ) (V : Fin n → ℕ) (t : ℕ) : ℝ≥0∞ :=
  ∑ i, ENNReal.ofReal (r i) * EEx (demand wt V t) (Xf i)

def rc (r : Fin n → ℝ) : Option (Fin n) → ℝ≥0∞
  | none => 0
  | some i => ENNReal.ofReal (r i)

lemma rc_eq (r : Fin n → ℝ) (c : Option (Fin n)) :
    rc r c = ∑ i, ENNReal.ofReal (r i) * (if c = some i then 1 else 0) := by
  rcases c with _ | j
  · simp [rc]
  · simp only [rc, Option.some.injEq, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp

lemma Fr_zero (wt : Weights n) (r : Fin n → ℝ) (V : Fin n → ℕ) : Fr wt r V 0 = 0 := by
  unfold Fr
  simp [demand_zero, EEx_pure, Xf]

lemma Fr_succ (wt : Weights n) (r : Fin n → ℝ) (V : Fin n → ℕ) (t : ℕ) :
    Fr wt r V (t + 1) = ∑ c, step wt V c * (Fr wt r (sb1 V c) t + rc r c) := by
  unfold Fr
  have e : ∀ i, EEx (demand wt V (t + 1)) (Xf i) = ∑ c, step wt V c *
      (EEx (demand wt (sb1 V c) t) (Xf i) + (if c = some i then 1 else 0)) := by
    intro i
    rw [EEx_succ_bwd]
    apply Finset.sum_congr rfl
    intro c _
    rw [Xf_shf, EEx_add, EEx_const']
  simp_rw [e, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [rc_eq, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma Fr_le (wt : Weights n) (hw : wt.Pos) (r : Fin n → ℝ) (V : Fin n → ℕ) (t : ℕ) :
    Fr wt r V t ≤ ∑ i, ENNReal.ofReal (r i) * (V i : ℝ≥0∞) := by
  unfold Fr
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (by simp)
  rw [EX_min wt hw]
  apply EEx_le
  intro x
  exact_mod_cast min_le_right _ _

lemma Fr_ne_top (wt : Weights n) (hw : wt.Pos) (r : Fin n → ℝ) (V : Fin n → ℕ) (t : ℕ) :
    Fr wt r V t ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun i _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _)) (Fr_le wt hw r V t)

lemma Fr_toReal (wt : Weights n) (hw : wt.Pos) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (V : Fin n → ℕ) (t : ℕ) : (Fr wt r V t).toReal = ∑ i, r i * expXm wt V t i := by
  unfold Fr
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (EX_ne_top wt hw _ _ _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hr i), expXm_eq]


/-! ## The geometric-skip simulator -/

lemma Obl_drawGeom (g : ℝ) : Obl (drawGeom g) := by
  unfold drawGeom
  exact Obl_bind (Obl_charge 1) (fun _ => Obl_lift _)

lemma vl_drawGeom (g : ℝ) : vl (drawGeom g) = geomPMF g := by
  unfold drawGeom
  rw [vl_bind (Obl_charge 1) (fun _ => Obl_lift _), vl_charge, PMF.pure_bind, vl_lift]

lemma Obl_drawCat (p : List ℝ) : Obl (drawCat p) := by
  unfold drawCat
  exact Obl_bind (Obl_charge _) (fun _ => Obl_lift _)

lemma vl_drawCat (p : List ℝ) : vl (drawCat p) = catPMF p := by
  unfold drawCat
  rw [vl_bind (Obl_charge _) (fun _ => Obl_lift _), vl_charge, PMF.pure_bind, vl_lift]

section Sim

variable (wts : Weights n) (r : Fin n → ℝ)

noncomputable def stage4 (st : SimState n) (S : List (Fin n)) (T : ℕ) (k : ℕ) :
    Prog (SimState n) :=
  match S[k]? with
  | none => opn 1 { st with done := true }
  | some i =>
    opn 6 (SimState.mk (Function.update st.V i (st.V i - 1)) (st.t - (T + 1)) (st.Y + r i) false)

/-- The last stage of a round: after the geometric draw. -/
noncomputable def stage3 (st : SimState n) (S : List (Fin n)) (wS : ℝ) (T : ℕ) :
    Prog (SimState n) := do
  let late ← opn 2 (decide (st.t < T + 1))
  if late then opn 1 { st with done := true }
  else do
    let masses ← opn (2 * S.length + 1) (S.map fun i => wts.w i / wS)
    let k ← drawCat masses
    stage4 r st S T k

lemma Obl_stage4 (st : SimState n) (S : List (Fin n)) (T k : ℕ) : Obl (stage4 r st S T k) := by
  unfold stage4
  split
  · exact Obl_opn _ _
  · exact Obl_opn _ _

lemma vl_stage4 (st : SimState n) (S : List (Fin n)) (T k : ℕ) :
    vl (stage4 r st S T k) = (S[k]?).elim (PMF.pure { st with done := true })
      (fun i => PMF.pure (SimState.mk (Function.update st.V i (st.V i - 1)) (st.t - (T + 1))
          (st.Y + r i) false)) := by
  unfold stage4
  cases S[k]? <;> exact vl_opn _ _

lemma stage3_eq (st : SimState n) (S : List (Fin n)) (wS : ℝ) (T : ℕ) :
    stage3 wts r st S wS T = (opn 2 (decide (st.t < T + 1)) >>= fun late =>
      if late = true then opn 1 { st with done := true }
      else (opn (2 * S.length + 1) (S.map fun i => wts.w i / wS) >>= fun masses =>
        drawCat masses >>= fun k => stage4 r st S T k)) := rfl

lemma Obl_stage3 (st : SimState n) (S : List (Fin n)) (wS : ℝ) (T : ℕ) :
    Obl (stage3 wts r st S wS T) := by
  rw [stage3_eq]
  refine Obl_bind (Obl_opn _ _) (fun late => ?_)
  refine Obl_ite _ (Obl_opn _ _) ?_
  exact Obl_bind (Obl_opn _ _) (fun masses => Obl_bind (Obl_drawCat _) (fun k => Obl_stage4 r st S T k))

lemma vl_stage3 (st : SimState n) (S : List (Fin n)) (wS : ℝ) (T : ℕ) :
    vl (stage3 wts r st S wS T) =
      if st.t < T + 1 then PMF.pure { st with done := true }
      else (catPMF (S.map fun i => wts.w i / wS)).bind fun k => vl (stage4 r st S T k) := by
  rw [stage3_eq, vl_bind (Obl_opn _ _) (fun late => Obl_ite _ (Obl_opn _ _)
    (Obl_bind (Obl_opn _ _) (fun masses => Obl_bind (Obl_drawCat _)
      (fun k => Obl_stage4 r st S T k)))), vl_opn, PMF.pure_bind]
  by_cases hl : st.t < T + 1
  · simp only [hl, decide_true, ↓reduceIte]
    exact vl_opn _ _
  · simp only [hl, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [vl_bind (Obl_opn _ _) (fun masses => Obl_bind (Obl_drawCat _)
      (fun k => Obl_stage4 r st S T k)), vl_opn, PMF.pure_bind,
      vl_bind (Obl_drawCat _) (fun k => Obl_stage4 r st S T k), vl_drawCat]

lemma simRound_eq (st : SimState n) (hd : st.done = false) :
    simRound wts r st =
      (opn (2 * n + 2) ((List.finRange n).filter fun i => 0 < st.V i) >>= fun S =>
        opn (2 * n + 2) (S.map wts.w).sum >>= fun wS =>
          opn 2 (decide (S = [] ∨ st.t = 0)) >>= fun ended =>
            if ended = true then opn 1 { st with done := true }
            else (opn 2 (wS / (wts.w0 + wS)) >>= fun g =>
              drawGeom g >>= fun T => stage3 wts r st S wS T)) := by
  unfold simRound
  rw [if_neg (by simp [hd])]
  rfl

lemma Obl_simRound (st : SimState n) : Obl (simRound wts r st) := by
  by_cases hd : st.done = true
  · unfold simRound
    rw [if_pos hd]
    exact Obl_opn _ _
  · rw [simRound_eq wts r st (by simpa using hd)]
    refine Obl_bind (Obl_opn _ _) (fun S => Obl_bind (Obl_opn _ _) (fun wS =>
      Obl_bind (Obl_opn _ _) (fun ended => Obl_ite _ (Obl_opn _ _) ?_)))
    exact Obl_bind (Obl_opn _ _) (fun g => Obl_bind (Obl_drawGeom g)
      (fun T => Obl_stage3 wts r st _ _ T))

lemma vl_simRound_done (st : SimState n) (hd : st.done = true) :
    vl (simRound wts r st) = PMF.pure st := by
  unfold simRound
  rw [if_pos hd]
  exact vl_opn _ _

lemma vl_simRound_nd (st : SimState n) (hd : st.done = false) :
    vl (simRound wts r st) =
      if ((List.finRange n).filter fun i => 0 < st.V i) = [] ∨ st.t = 0 then
        PMF.pure { st with done := true }
      else (geomPMF ((((List.finRange n).filter fun i => 0 < st.V i).map wts.w).sum /
          (wts.w0 + (((List.finRange n).filter fun i => 0 < st.V i).map wts.w).sum))).bind
        fun T => vl (stage3 wts r st ((List.finRange n).filter fun i => 0 < st.V i)
          (((List.finRange n).filter fun i => 0 < st.V i).map wts.w).sum T) := by
  rw [simRound_eq wts r st hd]
  rw [vl_bind (Obl_opn _ _) (fun S => Obl_bind (Obl_opn _ _) (fun wS =>
      Obl_bind (Obl_opn _ _) (fun ended => Obl_ite _ (Obl_opn _ _)
        (Obl_bind (Obl_opn _ _) (fun g => Obl_bind (Obl_drawGeom g)
          (fun T => Obl_stage3 wts r st _ _ T)))))), vl_opn, PMF.pure_bind]
  rw [vl_bind (Obl_opn _ _) (fun wS =>
      Obl_bind (Obl_opn _ _) (fun ended => Obl_ite _ (Obl_opn _ _)
        (Obl_bind (Obl_opn _ _) (fun g => Obl_bind (Obl_drawGeom g)
          (fun T => Obl_stage3 wts r st _ _ T))))), vl_opn, PMF.pure_bind]
  rw [vl_bind (Obl_opn _ _) (fun ended => Obl_ite _ (Obl_opn _ _)
        (Obl_bind (Obl_opn _ _) (fun g => Obl_bind (Obl_drawGeom g)
          (fun T => Obl_stage3 wts r st _ _ T)))), vl_opn, PMF.pure_bind]
  by_cases he : ((List.finRange n).filter fun i => 0 < st.V i) = [] ∨ st.t = 0
  · simp only [he, decide_true, ↓reduceIte]
    exact vl_opn _ _
  · simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [vl_bind (Obl_opn _ _) (fun g => Obl_bind (Obl_drawGeom g)
          (fun T => Obl_stage3 wts r st _ _ T)), vl_opn, PMF.pure_bind,
      vl_bind (Obl_drawGeom _) (fun T => Obl_stage3 wts r st _ _ T), vl_drawGeom]

end Sim


/-! ## Unrolling the demand recursion into geometric skips -/

section Unroll

variable (wts : Weights n) (r : Fin n → ℝ)

abbrev inS (V : Fin n → ℕ) : List (Fin n) := (List.finRange n).filter fun i => 0 < V i

lemma inS_nodup (V : Fin n → ℕ) : (inS V).Nodup := (List.nodup_finRange n).filter _

lemma inS_toFinset (V : Fin n → ℕ) : (inS V).toFinset = inStock V := by
  ext i
  simp [inS, inStock]

lemma list_sum_inS {M : Type*} [AddCommMonoid M] (V : Fin n → ℕ) (f : Fin n → M) :
    ((inS V).map f).sum = ∑ i ∈ inStock V, f i := by
  rw [← inS_toFinset, List.sum_toFinset _ (inS_nodup V)]

noncomputable abbrev wSum (V : Fin n → ℕ) : ℝ := ((inS V).map wts.w).sum

lemma wSum_eq (V : Fin n → ℕ) : wSum wts V = wts.wsum (inStock V) := by
  unfold wSum Weights.wsum
  exact list_sum_inS V wts.w

noncomputable def Phi (V : Fin n → ℕ) (s : ℕ) : ℝ≥0∞ :=
  ∑ i ∈ inStock V, ENNReal.ofReal (wts.w i / wSum wts V) *
    (Fr wts r (V - Pi.single i 1) s + ENNReal.ofReal (r i))

lemma Fr_step (hw : wts.Pos) (V : Fin n → ℕ) (hV : inS V ≠ []) (t : ℕ) :
    Fr wts r V (t + 1) = ENNReal.ofReal (1 - wSum wts V / (wts.w0 + wSum wts V)) * Fr wts r V t +
      ENNReal.ofReal (wSum wts V / (wts.w0 + wSum wts V)) * Phi wts r V t := by
  have hS0 : 0 ≤ wSum wts V := by rw [wSum_eq]; exact wsum_nonneg wts hw V
  have hZ : 0 < wts.w0 + wSum wts V := by linarith [hw.1]
  rw [Fr_succ, Fintype.sum_option]
  have hnone : step wts V none = ENNReal.ofReal (1 - wSum wts V / (wts.w0 + wSum wts V)) := by
    rw [step_eq wts hw, ZZ_eq, ← wSum_eq]
    congr 1
    simp only [qq]
    field_simp
    ring
  rw [hnone]
  simp only [sb1, rc, add_zero]
  congr 1
  unfold Phi
  rw [Finset.mul_sum]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => 0 < V i)]
  have h0 : ∑ i ∈ Finset.univ.filter (fun i => ¬ 0 < V i),
      step wts V (some i) * (Fr wts r (V - Pi.single i 1) t + ENNReal.ofReal (r i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [step_eq wts hw]
    simp [qq, hi.2]
  rw [h0, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_filter] at hi
  rw [step_eq wts hw, ZZ_eq, ← wSum_eq, ← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg hS0 hZ.le)]
  congr 2
  simp only [qq, if_pos hi.2]
  have hS : 0 < wSum wts V := by
    unfold wSum
    obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil _ hV
    have hjpos : 0 < wts.w j := hw.2 j
    have := List.single_le_sum (fun x hx => by
      obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx
      exact (hw.2 y).le) (wts.w j) (List.mem_map.2 ⟨j, hj, rfl⟩)
    linarith
  field_simp

lemma Fr_unroll (hw : wts.Pos) (V : Fin n → ℕ) (hV : inS V ≠ []) : ∀ t,
    Fr wts r V t = ∑ T ∈ Finset.range t,
      ENNReal.ofReal ((1 - wSum wts V / (wts.w0 + wSum wts V)) ^ T *
        (wSum wts V / (wts.w0 + wSum wts V))) * Phi wts r V (t - 1 - T) := by
  have hS0 : 0 ≤ wSum wts V := by rw [wSum_eq]; exact wsum_nonneg wts hw V
  have hZ : 0 < wts.w0 + wSum wts V := by linarith [hw.1]
  have hg0 : 0 ≤ wSum wts V / (wts.w0 + wSum wts V) := div_nonneg hS0 hZ.le
  have hg1 : 0 ≤ 1 - wSum wts V / (wts.w0 + wSum wts V) := by
    rw [sub_nonneg, div_le_one hZ]
    linarith [hw.1]
  intro t
  induction t with
  | zero => simp [Fr_zero]
  | succ t ih =>
    rw [Fr_step wts r hw V hV t, ih, Finset.sum_range_succ', Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro T hT
      rw [Finset.mem_range] at hT
      rw [show t + 1 - 1 - (T + 1) = t - 1 - T by omega, ← mul_assoc,
        ← ENNReal.ofReal_mul hg1, pow_succ]
      congr 2
      ring
    · simp

end Unroll

/-! ## Iterated rounds -/

section Rounds

variable (wts : Weights n) (r : Fin n → ℝ)

noncomputable def iterR (k : ℕ) (st : SimState n) : Prog (SimState n) :=
  foldP (List.range k) (fun st _ => simRound wts r st) st

lemma foldP_ignore {β α : Type} (g : β → Prog β) :
    ∀ (l l' : List α), l.length = l'.length → ∀ b,
      foldP l (fun st _ => g st) b = foldP l' (fun st _ => g st) b
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l, a' :: l', h, b => by
    show (charge 1 >>= fun _ => (g b >>= fun b' => foldP l (fun st _ => g st) b')) =
      (charge 1 >>= fun _ => (g b >>= fun b' => foldP l' (fun st _ => g st) b'))
    have h' : l.length = l'.length := by simpa using h
    congr 1
    funext _
    congr 1
    funext b'
    exact foldP_ignore g l l' h' b'

lemma Obl_iterR (k : ℕ) (st : SimState n) : Obl (iterR wts r k st) :=
  Obl_foldP _ (fun st _ => Obl_simRound wts r st) _ st

lemma vl_iterR_succ (k : ℕ) (st : SimState n) :
    vl (iterR wts r (k + 1) st) = (vl (simRound wts r st)).bind (fun st' => vl (iterR wts r k st')) := by
  have e : iterR wts r (k + 1) st = (charge 1 >>= fun _ =>
      (simRound wts r st >>= fun st' => iterR wts r k st')) := by
    unfold iterR
    rw [List.range_succ_eq_map]
    show (charge 1 >>= fun _ => (simRound wts r st >>= fun b' =>
      foldP ((List.range k).map Nat.succ) (fun st _ => simRound wts r st) b')) = _
    congr 1
    funext _
    congr 1
    funext b'
    exact foldP_ignore (simRound wts r) _ _ (by simp) b'
  rw [e, vl_bind (Obl_charge 1) (fun _ => Obl_bind (Obl_simRound wts r st)
    (fun st' => Obl_iterR wts r k st')), vl_charge, PMF.pure_bind,
    vl_bind (Obl_simRound wts r st) (fun st' => Obl_iterR wts r k st')]

lemma vl_iterR_zero (st : SimState n) : vl (iterR wts r 0 st) = PMF.pure st := by
  unfold iterR
  exact vl_pure st

noncomputable def Esim (k : ℕ) (st : SimState n) : ℝ≥0∞ :=
  EEx (vl (iterR wts r k st)) (fun s => ENNReal.ofReal s.Y)

lemma Esim_done : ∀ (k : ℕ) (st : SimState n), st.done = true → Esim wts r k st = ENNReal.ofReal st.Y := by
  intro k
  induction k with
  | zero => intro st _; unfold Esim; rw [vl_iterR_zero, EEx_pure]
  | succ k ih =>
    intro st hd
    unfold Esim
    rw [vl_iterR_succ, vl_simRound_done wts r st hd, PMF.pure_bind]
    exact ih st hd

end Rounds


/-! ## The simulator computes the expected revenue -/

section SimMain

variable (wts : Weights n) (r : Fin n → ℝ)

lemma update_eq_sub (V : Fin n → ℕ) (i : Fin n) :
    Function.update V i (V i - 1) = V - Pi.single i 1 := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · rw [Function.update_of_ne hj]
    simp [Pi.single_apply, hj]

lemma wSum_pos (hw : wts.Pos) (V : Fin n → ℕ) (hV : inS V ≠ []) : 0 < wSum wts V := by
  unfold wSum
  obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil _ hV
  have := List.single_le_sum (fun x hx => by
    obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx
    exact (hw.2 y).le) (wts.w j) (List.mem_map.2 ⟨j, hj, rfl⟩)
  linarith [hw.2 j]

lemma sum_range_list {α β : Type*} [AddCommMonoid β] (G : α → β) :
    ∀ (S : List α) (F : ℕ → β), (∀ k (hk : k < S.length), F k = G (S[k])) →
      ∑ k ∈ Finset.range S.length, F k = (S.map G).sum
  | [], F, _ => by simp
  | a :: S, F, hF => by
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons,
      sum_range_list G S (fun k => F (k + 1)) (fun k hk => by
        rw [hF (k + 1) (by simp; omega)]
        rfl), hF 0 (by simp)]
    rw [add_comm]
    rfl

lemma cat_expect (hw : wts.Pos) (V : Fin n → ℕ) (hV : inS V ≠ []) (c : ℝ≥0∞)
    (f : Fin n → ℝ≥0∞) :
    ∑' k, catPMF ((inS V).map fun i => wts.w i / wSum wts V) k *
        ((inS V)[k]?).elim c f =
      ∑ i ∈ inStock V, ENNReal.ofReal (wts.w i / wSum wts V) * f i := by
  have hS := wSum_pos wts hw V hV
  have hnn : ∀ x ∈ (inS V).map (fun i => wts.w i / wSum wts V), 0 ≤ x := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx
    exact div_nonneg (hw.2 y).le hS.le
  have hsum : ((inS V).map fun i => wts.w i / wSum wts V).sum = 1 := by
    rw [list_sum_inS V (fun i => wts.w i / wSum wts V), ← Finset.sum_div]
    have : ∑ i ∈ inStock V, wts.w i = wSum wts V := by
      rw [wSum_eq]
      rfl
    rw [this, div_self hS.ne']
  simp_rw [catPMF_apply _ hnn hsum]
  rw [tsum_eq_sum (s := Finset.range (inS V).length)]
  · rw [← list_sum_inS V (fun i => ENNReal.ofReal (wts.w i / wSum wts V) * f i)]
    apply sum_range_list
    intro k hk
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
      List.getElem?_eq_getElem hk, Option.elim_some]
  · intro k hk
    rw [Finset.mem_range, not_lt] at hk
    rw [List.getD_eq_default _ _ (by simpa using hk), ENNReal.ofReal_zero, zero_mul]

lemma ofReal_ratio_sum (hw : wts.Pos) (V : Fin n → ℕ) (hV : inS V ≠ []) :
    ∑ i ∈ inStock V, ENNReal.ofReal (wts.w i / wSum wts V) = 1 := by
  have hS := wSum_pos wts hw V hV
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => div_nonneg (hw.2 i).le hS.le),
    ← Finset.sum_div]
  have : ∑ i ∈ inStock V, wts.w i = wSum wts V := by
    rw [wSum_eq]
    rfl
  rw [this, div_self hS.ne', ENNReal.ofReal_one]

lemma Fr_noStock (hw : wts.Pos) (V : Fin n → ℕ) (hV : inS V = []) (t : ℕ) :
    Fr wts r V t = 0 := by
  have hz : ∀ i, V i = 0 := by
    intro i
    by_contra h
    have : i ∈ inS V := by
      simp only [inS, List.mem_filter, List.mem_finRange, true_and]
      exact decide_eq_true (Nat.pos_of_ne_zero h)
    rw [hV] at this
    simp at this
  have := Fr_le wts hw r V t
  simp only [hz, Nat.cast_zero, mul_zero, Finset.sum_const_zero, nonpos_iff_eq_zero] at this
  exact this

theorem Esim_main (hw : wts.Pos) (hr : ∀ i, 0 ≤ r i) : ∀ (k : ℕ) (st : SimState n),
    st.done = false → 0 ≤ st.Y → (∑ i, st.V i) + 1 ≤ k →
      Esim wts r k st = ENNReal.ofReal st.Y + Fr wts r st.V st.t := by
  intro k
  induction k with
  | zero => intro st _ _ hk; omega
  | succ k ih =>
    intro st hd hY hk
    unfold Esim
    rw [vl_iterR_succ, vl_simRound_nd wts r st hd]
    by_cases he : inS st.V = [] ∨ st.t = 0
    · rw [if_pos he, PMF.pure_bind]
      have h1 := Esim_done wts r k { st with done := true } rfl
      unfold Esim at h1
      rw [h1]
      rcases he with he | he
      · rw [Fr_noStock wts r hw _ he, add_zero]
      · rw [he, Fr_zero, add_zero]
    · rw [if_neg he]
      push_neg at he
      obtain ⟨hV, ht⟩ := he
      have hS := wSum_pos wts hw st.V hV
      have hZ : 0 < wts.w0 + wSum wts st.V := by linarith [hw.1]
      have hg0 : 0 < wSum wts st.V / (wts.w0 + wSum wts st.V) := div_pos hS hZ
      have hg1 : wSum wts st.V / (wts.w0 + wSum wts st.V) ≤ 1 := by
        rw [div_le_one hZ]
        linarith [hw.1]
      rw [PMF.bind_bind, EEx_bind]
      have hT : ∀ T : ℕ, EEx (vl (stage3 wts r st (inS st.V) (wSum wts st.V) T))
          (fun s => EEx (vl (iterR wts r k s)) (fun s' => ENNReal.ofReal s'.Y)) =
          ENNReal.ofReal st.Y + (if st.t < T + 1 then 0 else Phi wts r st.V (st.t - (T + 1))) := by
        intro T
        rw [vl_stage3]
        by_cases hl : st.t < T + 1
        · rw [if_pos hl, if_pos hl, EEx_pure, add_zero]
          have h1 := Esim_done wts r k { st with done := true } rfl
          unfold Esim at h1
          exact h1
        · rw [if_neg hl, if_neg hl, EEx_bind]
          have hcase : ∀ k', EEx (vl (stage4 r st (inS st.V) T k'))
              (fun s => EEx (vl (iterR wts r k s)) (fun s' => ENNReal.ofReal s'.Y)) =
              ((inS st.V)[k']?).elim (ENNReal.ofReal st.Y) (fun i => ENNReal.ofReal st.Y +
                ENNReal.ofReal (r i) + Fr wts r (st.V - Pi.single i 1) (st.t - (T + 1))) := by
            intro k'
            rw [vl_stage4]
            cases hk' : (inS st.V)[k']? with
            | none =>
              simp only [Option.elim_none]
              rw [EEx_pure]
              have h1 := Esim_done wts r k { st with done := true } rfl
              unfold Esim at h1
              exact h1
            | some i =>
              simp only [Option.elim_some]
              rw [EEx_pure]
              have hi : i ∈ inS st.V := List.mem_of_getElem? hk'
              have hVi : 0 < st.V i := by
                simp only [inS, List.mem_filter] at hi
                simpa using hi.2
              have hsum : (∑ j, (Function.update st.V i (st.V i - 1)) j) + 1 ≤ k := by
                have hs : ∑ j, st.V j = (∑ j, (Function.update st.V i (st.V i - 1)) j) + 1 := by
                  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
                    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
                  rw [Function.update_self]
                  have : ∑ x ∈ Finset.univ.erase i, Function.update st.V i (st.V i - 1) x =
                      ∑ x ∈ Finset.univ.erase i, st.V x :=
                    Finset.sum_congr rfl (fun x hx =>
                      Function.update_of_ne (Finset.ne_of_mem_erase hx) _ _)
                  rw [this]
                  omega
                omega
              have := ih (SimState.mk (Function.update st.V i (st.V i - 1)) (st.t - (T + 1))
                (st.Y + r i) false) rfl (by simp only []; linarith [hr i]) hsum
              unfold Esim at this
              rw [this]
              simp only []
              rw [ENNReal.ofReal_add hY (hr i), update_eq_sub]
          simp_rw [hcase]
          rw [cat_expect wts hw st.V hV]
          unfold Phi
          conv_rhs => rw [show ENNReal.ofReal st.Y = (∑ i ∈ inStock st.V,
            ENNReal.ofReal (wts.w i / wSum wts st.V)) * ENNReal.ofReal st.Y by
              rw [ofReal_ratio_sum wts hw st.V hV, one_mul]]
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
      have hT' : ∀ T : ℕ, EEx ((vl (stage3 wts r st (inS st.V) (wSum wts st.V) T)).bind
          fun st' => vl (iterR wts r k st')) (fun s => ENNReal.ofReal s.Y) =
          ENNReal.ofReal st.Y + (if st.t < T + 1 then 0 else Phi wts r st.V (st.t - (T + 1))) := by
        intro T
        rw [EEx_bind]
        exact hT T
      simp_rw [hT']
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      congr 1
      rw [Fr_unroll wts r hw st.V hV st.t]
      rw [tsum_eq_sum (s := Finset.range st.t)]
      · apply Finset.sum_congr rfl
        intro T hT
        rw [Finset.mem_range] at hT
        rw [if_neg (by omega), geomPMF_apply _ hg0 hg1, show st.t - (T + 1) = st.t - 1 - T by omega]
      · intro T hT
        rw [Finset.mem_range, not_lt] at hT
        rw [if_pos (by omega), mul_zero]

end SimMain


/-! ## The simulator: mean and range of one simulated revenue -/

section SimFacts

variable (wts : Weights n) (r : Fin n → ℝ)

lemma simulate_eq (U : Fin n → ℕ) (m nU : ℕ) :
    simulate wts r U m nU =
      (iterR wts r (nU + 1) (SimState.mk U m 0 false) >>= fun st => pure st.Y) := rfl

lemma Obl_simulate (U : Fin n → ℕ) (m nU : ℕ) : Obl (simulate wts r U m nU) := by
  rw [simulate_eq]
  exact Obl_bind (Obl_iterR wts r _ _) (fun _ => Obl_pure _)

lemma vl_simulate (U : Fin n → ℕ) (m nU : ℕ) :
    vl (simulate wts r U m nU) = (vl (iterR wts r (nU + 1) (SimState.mk U m 0 false))).bind
      (fun st => PMF.pure st.Y) := by
  rw [simulate_eq, vl_bind (Obl_iterR wts r _ _) (fun _ => Obl_pure _)]
  simp only [vl_pure]

lemma E_simulate (hw : wts.Pos) (hr : ∀ i, 0 ≤ r i) (U : Fin n → ℕ) (m : ℕ) :
    EEx (vl (simulate wts r U m (norm1 U))) (fun y => ENNReal.ofReal y) = Fr wts r U m := by
  rw [vl_simulate, EEx_bind]
  simp_rw [EEx_pure]
  have h := Esim_main wts r hw hr (norm1 U + 1) (SimState.mk U m 0 false) rfl le_rfl
    (by unfold norm1; exact le_rfl)
  unfold Esim at h
  dsimp only at h
  rw [ENNReal.ofReal_zero, zero_add] at h
  exact h

/-- The invariant of a simulated run: stock only decreases, revenue is non-negative, and every
unit sold earned at most `rs`. -/
def SInv (U : Fin n → ℕ) (rs : ℝ) (st : SimState n) : Prop :=
  (∀ i, st.V i ≤ U i) ∧ 0 ≤ st.Y ∧ st.Y + (∑ i, (st.V i : ℝ)) * rs ≤ (∑ i, (U i : ℝ)) * rs

lemma SInv_round (U : Fin n → ℕ) (rs : ℝ) (hrs : ∀ i, 0 < U i → r i ≤ rs)
    (hr : ∀ i, 0 ≤ r i) (st : SimState n) (hst : SInv U rs st) (x : SimState n)
    (hx : x ∈ (vl (simRound wts r st)).support) : SInv U rs x := by
  cases hd : st.done
  · rw [vl_simRound_nd wts r st hd] at hx
    split_ifs at hx with he
    · rw [PMF.support_pure, Set.mem_singleton_iff] at hx
      subst hx
      exact hst
    · rw [PMF.mem_support_bind_iff] at hx
      obtain ⟨T, _, hx⟩ := hx
      rw [vl_stage3] at hx
      split_ifs at hx with hl
      · rw [PMF.support_pure, Set.mem_singleton_iff] at hx
        subst hx
        exact hst
      · rw [PMF.mem_support_bind_iff] at hx
        obtain ⟨k, _, hx⟩ := hx
        rw [vl_stage4] at hx
        cases hk : ((List.finRange n).filter fun i => 0 < st.V i)[k]? with
        | none =>
          rw [hk, Option.elim_none, PMF.support_pure, Set.mem_singleton_iff] at hx
          subst hx
          exact hst
        | some i =>
          rw [hk, Option.elim_some, PMF.support_pure, Set.mem_singleton_iff] at hx
          subst hx
          have hi := List.mem_of_getElem? hk
          have hVi : 0 < st.V i := by
            simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hi
            exact hi
          obtain ⟨h1, h2, h3⟩ := hst
          refine ⟨fun j => ?_, ?_, ?_⟩
          · show Function.update st.V i (st.V i - 1) j ≤ U j
            by_cases hj : j = i
            · subst hj
              rw [Function.update_self]
              exact (Nat.sub_le _ _).trans (h1 j)
            · rw [Function.update_of_ne hj]
              exact h1 j
          · show 0 ≤ st.Y + r i
            linarith [hr i]
          · show st.Y + r i + (∑ j, ((Function.update st.V i (st.V i - 1) j : ℕ) : ℝ)) * rs ≤ _
            have hs : (∑ j, ((Function.update st.V i (st.V i - 1) j : ℕ) : ℝ)) =
                (∑ j, (st.V j : ℝ)) - 1 := by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
                ← Finset.add_sum_erase (s := Finset.univ) (fun j => (st.V j : ℝ))
                  (Finset.mem_univ i)]
              rw [Function.update_self]
              have : ∑ x ∈ Finset.univ.erase i,
                  ((Function.update st.V i (st.V i - 1) x : ℕ) : ℝ) =
                  ∑ x ∈ Finset.univ.erase i, (st.V x : ℝ) :=
                Finset.sum_congr rfl (fun x hx => by
                  rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)])
              rw [this, Nat.cast_sub (by omega)]
              push_cast
              ring
            rw [hs]
            have := hrs i (lt_of_lt_of_le hVi (h1 i))
            nlinarith
  · rw [vl_simRound_done wts r st hd, PMF.support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact hst

lemma SInv_iter (U : Fin n → ℕ) (rs : ℝ) (hrs : ∀ i, 0 < U i → r i ≤ rs)
    (hr : ∀ i, 0 ≤ r i) : ∀ (k : ℕ) (st : SimState n), SInv U rs st →
      ∀ x ∈ (vl (iterR wts r k st)).support, SInv U rs x := by
  intro k
  induction k with
  | zero =>
    intro st hst x hx
    rw [vl_iterR_zero, PMF.support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact hst
  | succ k ih =>
    intro st hst x hx
    rw [vl_iterR_succ, PMF.mem_support_bind_iff] at hx
    obtain ⟨y, hy, hx⟩ := hx
    exact ih y (SInv_round wts r U rs hrs hr st hst y hy) x hx

lemma simulate_range (U : Fin n → ℕ) (m : ℕ) (rs : ℝ) (hrs : ∀ i, 0 < U i → r i ≤ rs)
    (hr : ∀ i, 0 ≤ r i) (hrs0 : 0 ≤ rs) :
    ∀ y ∈ (vl (simulate wts r U m (norm1 U))).support, 0 ≤ y ∧ y ≤ (norm1 U : ℝ) * rs := by
  intro y hy
  rw [vl_simulate, PMF.mem_support_bind_iff] at hy
  obtain ⟨x, hx, hy⟩ := hy
  rw [PMF.support_pure, Set.mem_singleton_iff] at hy
  subst hy
  have h0 : SInv U rs (SimState.mk U m 0 false) := ⟨fun i => le_rfl, le_rfl, by simp⟩
  obtain ⟨_, h2, h3⟩ := SInv_iter wts r U rs hrs hr _ _ h0 x hx
  refine ⟨h2, ?_⟩
  have : (0 : ℝ) ≤ (∑ i, (x.V i : ℝ)) * rs :=
    mul_nonneg (Finset.sum_nonneg fun i _ => Nat.cast_nonneg _) hrs0
  have hn : ((norm1 U : ℕ) : ℝ) = ∑ i, (U i : ℝ) := by
    unfold norm1
    push_cast
    rfl
  rw [hn]
  linarith

lemma Fr_lower (hw : wts.Pos) (hr : ∀ i, 0 ≤ r i) (V : Fin n → ℕ) (t : ℕ) (ht : 1 ≤ t)
    (i : Fin n) (hVi : 0 < V i) :
    wts.w i / (wts.w0 + wts.wsum (inStock V)) * r i ≤ (Fr wts r V t).toReal := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have hle : step wts V (some i) * ENNReal.ofReal (r i) ≤ Fr wts r V (t' + 1) := by
    rw [Fr_succ]
    calc step wts V (some i) * ENNReal.ofReal (r i)
        ≤ step wts V (some i) * (Fr wts r (sb1 V (some i)) t' + rc r (some i)) := by
          apply mul_le_mul_of_nonneg_left _ zero_le
          show ENNReal.ofReal (r i) ≤ Fr wts r (sb1 V (some i)) t' + ENNReal.ofReal (r i)
          exact le_add_self
      _ ≤ ∑ c, step wts V c * (Fr wts r (sb1 V c) t' + rc r c) :=
          Finset.single_le_sum (f := fun c => step wts V c * (Fr wts r (sb1 V c) t' + rc r c))
            (fun c _ => zero_le) (Finset.mem_univ (some i))
  have h := ENNReal.toReal_mono (Fr_ne_top wts hw r V _) hle
  rw [ENNReal.toReal_mul, q_some wts hw V i hVi, ENNReal.toReal_ofReal (hr i)] at h
  exact h

lemma wsum_le_mul (hw : wts.Pos) (V : Fin n → ℕ) (W : ℝ) (hW : ∀ j, wts.w j ≤ W) :
    wts.wsum (inStock V) ≤ n * W := by
  refine (Wtot_ge wts hw V).trans ?_
  calc ∑ j, wts.w j ≤ ∑ _j : Fin n, W := Finset.sum_le_sum fun j _ => hW j
    _ = n * W := by simp

end SimFacts


open MeasureTheory

/-! ## Chernoff and Hoeffding bounds for sums of independent draws, in `PMF` form -/

section Hoeff

lemma EEx_ofReal_integral (ν : PMF ℝ) (f : ℝ → ℝ) (hf0 : ∀ y ∈ ν.support, 0 ≤ f y) (C : ℝ)
    (hC : ∀ y ∈ ν.support, f y ≤ C) (hfi : Integrable f ν.toMeasure) :
    EEx ν (fun y => ENNReal.ofReal (f y)) = ENNReal.ofReal (∫ y, f y ∂ν.toMeasure) := by
  rw [PMF.integral_eq_tsum ν f hfi]
  have hnn : ∀ y, 0 ≤ (ν y).toReal * f y := by
    intro y
    by_cases hy : y ∈ ν.support
    · exact mul_nonneg ENNReal.toReal_nonneg (hf0 y hy)
    · rw [PMF.mem_support_iff, not_not] at hy
      simp [hy]
  have hC0 : ∀ y, (ν y).toReal * f y ≤ C * (ν y).toReal := by
    intro y
    by_cases hy : y ∈ ν.support
    · rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hC y hy) ENNReal.toReal_nonneg
    · rw [PMF.mem_support_iff, not_not] at hy
      simp [hy]
  have hsum : Summable (fun y => (ν y).toReal * f y) := by
    refine Summable.of_nonneg_of_le hnn hC0 ?_
    exact (ENNReal.summable_toReal (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top)).mul_left C
  simp only [smul_eq_mul]
  rw [ENNReal.ofReal_tsum_of_nonneg hnn hsum]
  unfold EEx
  refine tsum_congr (fun y => ?_)
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (PMF.apply_ne_top ν y)]

lemma ae_Icc_of_support (ν : PMF ℝ) (a b : ℝ) (hs : ∀ y ∈ ν.support, a ≤ y ∧ y ≤ b) :
    ∀ᵐ y ∂ν.toMeasure, y ∈ Set.Icc a b := by
  rw [ae_iff]
  have e : {y : ℝ | ¬ y ∈ Set.Icc a b} = (Set.Icc a b)ᶜ := rfl
  rw [e, ν.toMeasure_apply_eq_zero_iff measurableSet_Icc.compl]
  exact Set.disjoint_left.2 fun y hy hy' => hy' (hs y hy)

lemma mean_ofReal (ν : PMF ℝ) (B : ℝ) (hs : ∀ y ∈ ν.support, 0 ≤ y ∧ y ≤ B) :
    EEx ν (fun y => ENNReal.ofReal y) = ENNReal.ofReal (∫ y, y ∂ν.toMeasure) := by
  have hb := ae_Icc_of_support ν 0 B hs
  have hm : AEMeasurable (fun y : ℝ => y) ν.toMeasure := measurable_id.aemeasurable
  have hi : Integrable (fun y : ℝ => y) ν.toMeasure := Integrable.of_mem_Icc 0 B hm hb
  exact EEx_ofReal_integral ν (fun y => y) (fun y hy => (hs y hy).1) B (fun y hy => (hs y hy).2) hi

lemma mean_nonneg (ν : PMF ℝ) (B : ℝ) (hs : ∀ y ∈ ν.support, 0 ≤ y ∧ y ≤ B) :
    0 ≤ ∫ y, y ∂ν.toMeasure := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_Icc_of_support ν 0 B hs] with y hy
  exact hy.1

lemma pmf_hoeffding (ν : PMF ℝ) (B : ℝ) (hB : 0 ≤ B) (hs : ∀ y ∈ ν.support, 0 ≤ y ∧ y ≤ B)
    (t : ℝ) : EEx ν (fun y => ENNReal.ofReal (Real.exp (t * y))) ≤
      ENNReal.ofReal (Real.exp (t * ∫ y, y ∂ν.toMeasure + B ^ 2 * t ^ 2 / 8)) := by
  have hb := ae_Icc_of_support ν 0 B hs
  have hm : AEMeasurable (fun y : ℝ => y) ν.toMeasure := measurable_id.aemeasurable
  have H := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc hm hb
  have hint := H.integrable_exp_mul t
  have h1 := H.mgf_le t
  generalize hmdef : ∫ y, y ∂ν.toMeasure = m at hint h1 ⊢
  have hfi : Integrable (fun y : ℝ => Real.exp (t * y)) ν.toMeasure := by
    have := hint.const_mul (Real.exp (t * m))
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    show Real.exp (t * m) * Real.exp (t * (y - m)) = Real.exp (t * y)
    rw [← Real.exp_add]
    congr 1
    ring
  rw [EEx_ofReal_integral ν (fun y => Real.exp (t * y)) (fun y _ => (Real.exp_pos _).le)
    (Real.exp (|t| * B))
    (fun y hy => Real.exp_le_exp.2 (by
      obtain ⟨h0, h1⟩ := hs y hy
      nlinarith [abs_nonneg t, le_abs_self t, neg_abs_le t])) hfi]
  apply ENNReal.ofReal_le_ofReal
  have e1 : ∫ y, Real.exp (t * y) ∂ν.toMeasure =
      Real.exp (t * m) * ∫ y, Real.exp (t * (y - m)) ∂ν.toMeasure := by
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [← Real.exp_add]
    congr 1
    ring
  rw [e1]
  have h1' : ∫ y, Real.exp (t * (y - m)) ∂ν.toMeasure ≤
      Real.exp (((‖B - 0‖₊ / 2) ^ 2 : NNReal) * t ^ 2 / 2) := h1
  refine (mul_le_mul_of_nonneg_left h1' (Real.exp_pos _).le).trans (le_of_eq ?_)
  rw [← Real.exp_add]
  congr 1
  norm_num [abs_of_nonneg hB]
  try ring

/-- The law of `a` plus the sum of `k` independent draws from `ν`. -/
noncomputable def sumLaw (ν : PMF ℝ) : ℕ → ℝ → PMF ℝ
  | 0, a => PMF.pure a
  | k + 1, a => ν.bind (fun y => sumLaw ν k (a + y))

lemma mgf_sumLaw (ν : PMF ℝ) (t : ℝ) : ∀ (k : ℕ) (a : ℝ),
    EEx (sumLaw ν k a) (fun z => ENNReal.ofReal (Real.exp (t * z))) =
      ENNReal.ofReal (Real.exp (t * a)) *
        (EEx ν (fun y => ENNReal.ofReal (Real.exp (t * y)))) ^ k := by
  intro k
  induction k with
  | zero =>
    intro a
    rw [sumLaw, EEx_pure, pow_zero, mul_one]
  | succ k ih =>
    intro a
    rw [sumLaw, EEx_bind]
    simp_rw [ih]
    have e : ∀ y, ENNReal.ofReal (Real.exp (t * (a + y))) =
        ENNReal.ofReal (Real.exp (t * a)) * ENNReal.ofReal (Real.exp (t * y)) := by
      intro y
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, mul_add]
    simp_rw [e]
    unfold EEx
    conv_rhs => rw [pow_succ, ← mul_assoc]
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun y => ?_
    ring

lemma sumLaw_support (ν : PMF ℝ) (B : ℝ) (hs : ∀ y ∈ ν.support, 0 ≤ y ∧ y ≤ B) :
    ∀ (k : ℕ) (a z : ℝ), z ∈ (sumLaw ν k a).support → a ≤ z ∧ z ≤ a + k * B := by
  intro k
  induction k with
  | zero =>
    intro a z hz
    rw [sumLaw, PMF.support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp
  | succ k ih =>
    intro a z hz
    rw [sumLaw, PMF.mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    obtain ⟨h1, h2⟩ := ih (a + y) z hz
    obtain ⟨h3, h4⟩ := hs y hy
    push_cast
    constructor <;> nlinarith

lemma tail_le (π : PMF ℝ) (A : Set ℝ) (g : ℝ → ℝ) (hg : ∀ z ∈ A, 0 ≤ g z) :
    π.toOuterMeasure A ≤ EEx π (fun z => ENNReal.ofReal (Real.exp (g z))) := by
  rw [PMF.toOuterMeasure_apply]
  unfold EEx
  refine ENNReal.tsum_le_tsum (fun z => ?_)
  by_cases hz : z ∈ A
  · rw [Set.indicator_of_mem hz]
    calc π z = π z * 1 := (mul_one _).symm
      _ ≤ π z * ENNReal.ofReal (Real.exp (g z)) := by
        apply mul_le_mul_of_nonneg_left _ zero_le
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (hg z hz))
  · rw [Set.indicator_of_notMem hz]
    exact zero_le

/-- One tail of the Chernoff–Hoeffding bound. -/
lemma chernoff_tail (ν : PMF ℝ) (B : ℝ) (hB : 0 < B) (hs : ∀ y ∈ ν.support, 0 ≤ y ∧ y ≤ B)
    (k : ℕ) (s : ℝ) (lam c : ℝ) (A : Set ℝ) (hA : ∀ z ∈ A, 0 ≤ lam * (z - c))
    (hlc : -lam * c + k * (lam * ∫ y, y ∂ν.toMeasure + B ^ 2 * lam ^ 2 / 8) ≤
      -2 * k * s ^ 2 / B ^ 2) :
    (sumLaw ν k 0).toOuterMeasure A ≤ ENNReal.ofReal (Real.exp (-2 * k * s ^ 2 / B ^ 2)) := by
  refine (tail_le _ A (fun z => lam * (z - c)) hA).trans ?_
  have e : ∀ z, ENNReal.ofReal (Real.exp (lam * (z - c))) =
      ENNReal.ofReal (Real.exp (-lam * c)) * ENNReal.ofReal (Real.exp (lam * z)) := by
    intro z
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  simp_rw [e]
  rw [EEx_const_mul, mgf_sumLaw, mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul]
  have hM := pmf_hoeffding ν B hB.le hs lam
  calc ENNReal.ofReal (Real.exp (-lam * c)) *
        EEx ν (fun y => ENNReal.ofReal (Real.exp (lam * y))) ^ k
      ≤ ENNReal.ofReal (Real.exp (-lam * c)) *
        ENNReal.ofReal (Real.exp (lam * ∫ y, y ∂ν.toMeasure + B ^ 2 * lam ^ 2 / 8)) ^ k := by
        gcongr
    _ = ENNReal.ofReal (Real.exp (-lam * c + k * (lam * ∫ y, y ∂ν.toMeasure +
          B ^ 2 * lam ^ 2 / 8))) := by
        rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    _ ≤ ENNReal.ofReal (Real.exp (-2 * k * s ^ 2 / B ^ 2)) :=
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hlc)

lemma chernoff_upper (ν : PMF ℝ) (B : ℝ) (hB : 0 < B) (hs : ∀ y ∈ ν.support, 0 ≤ y ∧ y ≤ B)
    (k : ℕ) (s : ℝ) (hs0 : 0 ≤ s) :
    (sumLaw ν k 0).toOuterMeasure {z | (k : ℝ) * (∫ y, y ∂ν.toMeasure + s) ≤ z} ≤
      ENNReal.ofReal (Real.exp (-2 * k * s ^ 2 / B ^ 2)) := by
  apply chernoff_tail ν B hB hs k s (4 * s / B ^ 2) ((k : ℝ) * (∫ y, y ∂ν.toMeasure + s))
  · intro z hz
    have : 0 ≤ 4 * s / B ^ 2 := by positivity
    exact mul_nonneg this (sub_nonneg.2 hz)
  · have hB0 : B ≠ 0 := hB.ne'
    apply le_of_eq
    field_simp
    ring

lemma chernoff_lower (ν : PMF ℝ) (B : ℝ) (hB : 0 < B) (hs : ∀ y ∈ ν.support, 0 ≤ y ∧ y ≤ B)
    (k : ℕ) (s : ℝ) (hs0 : 0 ≤ s) :
    (sumLaw ν k 0).toOuterMeasure {z | z ≤ (k : ℝ) * (∫ y, y ∂ν.toMeasure - s)} ≤
      ENNReal.ofReal (Real.exp (-2 * k * s ^ 2 / B ^ 2)) := by
  apply chernoff_tail ν B hB hs k s (-(4 * s / B ^ 2)) ((k : ℝ) * (∫ y, y ∂ν.toMeasure - s))
  · intro z hz
    have : 0 ≤ 4 * s / B ^ 2 := by positivity
    have hz' : z - (k : ℝ) * (∫ y, y ∂ν.toMeasure - s) ≤ 0 := sub_nonpos.2 hz
    nlinarith
  · have hB0 : B ≠ 0 := hB.ne'
    apply le_of_eq
    field_simp
    ring

lemma outer_add_compl (π : PMF ℝ) (A : Set ℝ) :
    π.toOuterMeasure A + π.toOuterMeasure Aᶜ = 1 := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
  simp_rw [Set.indicator_self_add_compl_apply]
  exact π.tsum_coe

end Hoeff


/-! ## Costs and deterministic values from every starting counter -/

def CA {α : Type} (p : Prog α) (K : ℕ) : Prop := ∀ s, ∀ x ∈ (p.run s).support, x.2 ≤ s + K

def VA {α : Type} (p : Prog α) (a : α) : Prop := ∀ s, ∀ x ∈ (p.run s).support, x.1 = a

lemma CA_mono {α : Type} {p : Prog α} {K K' : ℕ} (h : CA p K) (hK : K ≤ K') : CA p K' :=
  fun s x hx => (h s x hx).trans (by omega)

lemma CA_pure {α : Type} (a : α) : CA (pure a : Prog α) 0 := by
  intro s x hx
  have hx' : x ∈ (PMF.pure (a, s)).support := hx
  rw [PMF.mem_support_pure_iff] at hx'
  subst hx'
  simp

lemma VA_pure {α : Type} (a : α) : VA (pure a : Prog α) a := by
  intro s x hx
  have hx' : x ∈ (PMF.pure (a, s)).support := hx
  rw [PMF.mem_support_pure_iff] at hx'
  subst hx'
  rfl

lemma CA_charge (k : ℕ) : CA (charge k) k := by
  intro s x hx
  have hx' : x ∈ (PMF.pure ((), s + k)).support := hx
  rw [PMF.mem_support_pure_iff] at hx'
  subst hx'
  exact le_rfl

lemma VA_charge (k : ℕ) : VA (charge k) () := fun _ _ _ => rfl

lemma CA_lift {α : Type} (μ : PMF α) : CA (StateT.lift μ : Prog α) 0 := by
  intro s x hx
  have hx' : x ∈ (μ.bind (fun a => PMF.pure (a, s))).support := hx
  rw [PMF.mem_support_bind_iff] at hx'
  obtain ⟨a, _, ha⟩ := hx'
  rw [PMF.mem_support_pure_iff] at ha
  subst ha
  simp

lemma CA_bind {α β : Type} {p : Prog α} {f : α → Prog β} {K K' : ℕ} (hp : CA p K)
    (hf : ∀ a, CA (f a) K') : CA (p >>= f) (K + K') := by
  intro s x hx
  rw [run_bind', PMF.mem_support_bind_iff] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  have h1 := hp s y hy
  have h2 := hf y.1 y.2 x hxy
  omega

lemma CA_bind_val {α β : Type} {p : Prog α} {f : α → Prog β} {K K' : ℕ} {a : α} (hp : CA p K)
    (hv : VA p a) (hf : CA (f a) K') : CA (p >>= f) (K + K') := by
  intro s x hx
  rw [run_bind', PMF.mem_support_bind_iff] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  have h1 := hp s y hy
  rw [hv s y hy] at hxy
  have h2 := hf y.2 x hxy
  omega

lemma VA_bind_val {α β : Type} {p : Prog α} {f : α → Prog β} {a : α} {b : β}
    (hv : VA p a) (hf : VA (f a) b) : VA (p >>= f) b := by
  intro s x hx
  rw [run_bind', PMF.mem_support_bind_iff] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  rw [hv s y hy] at hxy
  exact hf y.2 x hxy

lemma CA_opn {α : Type} (k : ℕ) (a : α) : CA (opn k a) k := by
  unfold opn
  exact CA_mono (CA_bind (CA_charge k) (fun _ => CA_pure a)) (by omega)

lemma VA_opn {α : Type} (k : ℕ) (a : α) : VA (opn k a) a := by
  unfold opn
  exact VA_bind_val (VA_charge k) (VA_pure a)

lemma CA_ite {α : Type} (c : Prop) [Decidable c] {p q : Prog α} {K : ℕ} (hp : CA p K)
    (hq : CA q K) : CA (if c then p else q) K := by
  split_ifs
  · exact hp
  · exact hq

lemma CA_foldP {α β : Type} (f : β → α → Prog β) (K : ℕ) (hf : ∀ b a, CA (f b a) K) :
    ∀ (l : List α) (b : β), CA (foldP l f b) (l.length * (K + 1))
  | [], b => by
    simp only [List.length_nil, Nat.zero_mul]
    exact CA_pure b
  | a :: l, b => by
    show CA (charge 1 >>= fun _ => (f b a >>= fun b' => foldP l f b')) _
    refine CA_mono (CA_bind (CA_charge 1) (fun _ => CA_bind (hf b a)
      (fun b' => CA_foldP f K hf l b'))) ?_
    simp only [List.length_cons]
    exact le_of_eq (by ring)

lemma VA_foldP_opn {α β : Type} (k : ℕ) (f : β → α → β) :
    ∀ (l : List α) (b : β), VA (foldP l (fun acc x => opn k (f acc x)) b) (l.foldl f b)
  | [], b => VA_pure b
  | x :: l, b => by
    show VA (charge 1 >>= fun _ => (opn k (f b x) >>= fun b' =>
      foldP l (fun acc x => opn k (f acc x)) b')) _
    exact VA_bind_val (VA_charge 1) (VA_bind_val (VA_opn k _) (VA_foldP_opn k f l (f b x)))

lemma CA_drawGeom (g : ℝ) : CA (drawGeom g) 1 := by
  unfold drawGeom
  exact CA_mono (CA_bind (CA_charge 1) (fun _ => CA_lift _)) (by omega)

lemma CA_drawCat (p : List ℝ) : CA (drawCat p) (p.length + 1) := by
  unfold drawCat
  exact CA_mono (CA_bind (CA_charge _) (fun _ => CA_lift _)) (by omega)

lemma bind_congr_supp {α β : Type} (μ : PMF α) (f g : α → PMF β)
    (h : ∀ x ∈ μ.support, f x = g x) : μ.bind f = μ.bind g := by
  ext b
  simp only [PMF.bind_apply]
  refine tsum_congr fun x => ?_
  by_cases hx : μ x = 0
  · simp [hx]
  · rw [h x ((PMF.mem_support_iff _ _).2 hx)]

lemma vl_bind_val {α β : Type} {p : Prog α} {f : α → Prog β} {a : α} (hv : VA p a)
    (hf : Obl (f a)) : vl (p >>= f) = vl (f a) := by
  unfold vl
  rw [run_bind', PMF.map_bind]
  rw [bind_congr_supp (p.run 0) (fun x => ((f x.1).run x.2).map Prod.fst)
    (fun _ => ((f a).run 0).map Prod.fst) (fun x hx => by
      show ((f x.1).run x.2).map Prod.fst = ((f a).run 0).map Prod.fst
      rw [hv 0 x hx, hf x.2, PMF.map_comp]
      rfl)]
  exact PMF.bind_const _ _

/-! ## Costs of the simulator -/

section SimCost

variable (wts : Weights n) (r : Fin n → ℝ)

lemma CA_stage4 (st : SimState n) (S : List (Fin n)) (T k : ℕ) : CA (stage4 r st S T k) 6 := by
  unfold stage4
  split
  · exact CA_mono (CA_opn 1 _) (by omega)
  · exact CA_opn 6 _

lemma CA_stage3 (st : SimState n) (S : List (Fin n)) (wS : ℝ) (T : ℕ) :
    CA (stage3 wts r st S wS T) (3 * S.length + 10) := by
  rw [stage3_eq]
  refine CA_mono (CA_bind (K' := 3 * S.length + 8) (CA_opn 2 _) (fun late => CA_ite _
    (CA_mono (CA_opn 1 _) (by omega)) ?_)) (by omega)
  refine CA_mono (CA_bind_val (CA_opn _ _) (VA_opn _ _) (CA_bind (CA_drawCat _)
    (fun k => CA_stage4 r st S T k))) ?_
  simp only [List.length_map]
  omega

lemma CA_simRound (st : SimState n) : CA (simRound wts r st) (7 * n + 19) := by
  by_cases hd : st.done = true
  · unfold simRound
    rw [if_pos hd]
    exact CA_mono (CA_opn 1 st) (by omega)
  · rw [simRound_eq wts r st (by simpa using hd)]
    have hS : ((List.finRange n).filter fun i => 0 < st.V i).length ≤ n :=
      (List.length_filter_le _ _).trans (by simp)
    refine CA_mono (CA_bind_val (CA_opn _ _) (VA_opn _ _) (CA_bind_val (CA_opn _ _) (VA_opn _ _)
      (CA_bind (CA_opn 2 _) (fun ended => CA_ite _
        (K := 2 + (1 + (3 * ((List.finRange n).filter fun i => 0 < st.V i).length + 10)))
        (CA_mono (CA_opn 1 _) (by omega))
        (CA_bind (CA_opn 2 _) (fun g => CA_bind (CA_drawGeom g)
          (fun T => CA_stage3 wts r st _ _ T))))))) ?_
    omega

lemma CA_simulate (U : Fin n → ℕ) (m nU : ℕ) :
    CA (simulate wts r U m nU) ((nU + 1) * (7 * n + 20)) := by
  rw [simulate_eq]
  refine CA_mono (CA_bind (CA_foldP _ (7 * n + 19) (fun st _ => CA_simRound wts r st)
    (List.range (nU + 1)) _) (fun _ => CA_pure _)) ?_
  simp only [List.length_range, Nat.add_zero]
  exact le_of_eq (by ring)

end SimCost

/-! ## The estimator, step by step -/

section Est

variable (wts : Weights n) (r : Fin n → ℝ) (pM : ℕ →₀ ℝ) (U : Fin n → ℕ) (e δh : ℝ)

noncomputable def estBody (masses : List ℝ) (pos : List ℕ) (nU : ℕ) (acc : ℝ) : Prog ℝ := do
  let k ← drawCat masses
  let m ← opn 1 (pos.getD k 0)
  let Y ← simulate wts r U m nU
  opn 1 (acc + Y)

noncomputable def estR6 (masses : List ℝ) (pos : List ℕ) (ζ : ℕ) (P1 : ℝ) (nU : ℕ) : Prog ℝ :=
  foldP (List.range ζ) (fun acc _ => estBody wts r U masses pos nU acc) 0 >>= fun total =>
    opn 3 (P1 * (total / ζ))

noncomputable def estR5 (pos : List ℕ) (ζ : ℕ) (P1 : ℝ) (nU : ℕ) : Prog ℝ :=
  opn (2 * pos.length + 1) (pos.map fun m => pM m / P1) >>= fun masses =>
    estR6 wts r U masses pos ζ P1 nU

noncomputable def estR4 (supp : List ℕ) (ζ : ℕ) (P1 : ℝ) (nU : ℕ) : Prog ℝ :=
  opn (2 * supp.length + 1) (supp.filter (1 ≤ ·)) >>= fun pos => estR5 wts r pM U pos ζ P1 nU

noncomputable def estR3 (supp : List ℕ) (q : ℝ) (P1 : ℝ) (nU : ℕ) : Prog ℝ :=
  opn 10 ⌈((nU : ℝ) / (q * e)) ^ 2 * Real.log (2 / δh) / 2⌉₊ >>= fun ζ =>
    estR4 wts r pM U supp ζ P1 nU

noncomputable def estRq (supp : List ℕ) (wmax wmin : ℝ) (P1 : ℝ) (nU : ℕ) : Prog ℝ :=
  opn 3 (wmin / (wts.w0 + n * wmax)) >>= fun q => estR3 wts r pM U e δh supp q P1 nU

noncomputable def estR2 (supp : List ℕ) (wmax : ℝ) (P1 : ℝ) (nU : ℕ) : Prog ℝ :=
  foldP (List.finRange n) (fun acc i => opn 2 (min acc (wts.w i))) wmax >>= fun wmin =>
    estRq wts r pM U e δh supp wmax wmin P1 nU

noncomputable def estRest (supp : List ℕ) (P1 : ℝ) (nU : ℕ) : Prog ℝ :=
  foldP (List.finRange n) (fun acc i => opn 2 (max acc (wts.w i))) 0 >>= fun wmax =>
    estR2 wts r pM U e δh supp wmax P1 nU

noncomputable def estK3 (supp : List ℕ) (P1 : ℝ) (nU : ℕ) : Prog ℝ :=
  opn 2 (decide (P1 ≤ 0 ∨ nU = 0)) >>= fun triv =>
    if triv = true then pure 0 else estRest wts r pM U e δh supp P1 nU

noncomputable def estK2 (supp : List ℕ) (P1 : ℝ) : Prog ℝ :=
  foldP (List.finRange n) (fun acc i => opn 2 (acc + U i)) 0 >>= fun nU =>
    estK3 wts r pM U e δh supp P1 nU

noncomputable def estK1 (supp : List ℕ) : Prog ℝ :=
  foldP supp (fun acc m => opn 3 (if 1 ≤ m then acc + pM m else acc)) 0 >>= fun P1 =>
    estK2 wts r pM U e δh supp P1

lemma estimate_eq : estimate wts r pM U e δh =
    (opn (pM.support.card + 1) (pM.support.sort (· ≤ ·)) >>= fun supp =>
      estK1 wts r pM U e δh supp) := rfl

/-! ### Oblivious programs -/

lemma Obl_estBody (masses : List ℝ) (pos : List ℕ) (nU : ℕ) (acc : ℝ) :
    Obl (estBody wts r U masses pos nU acc) := by
  unfold estBody
  exact Obl_bind (Obl_drawCat _) (fun k => Obl_bind (Obl_opn _ _) (fun m =>
    Obl_bind (Obl_simulate wts r U m nU) (fun Y => Obl_opn _ _)))

lemma Obl_loop (masses : List ℝ) (pos : List ℕ) (nU : ℕ) (l : List ℕ) (a : ℝ) :
    Obl (foldP l (fun acc _ => estBody wts r U masses pos nU acc) a) :=
  Obl_foldP _ (fun acc _ => Obl_estBody wts r U masses pos nU acc) l a

lemma Obl_estR6 (masses : List ℝ) (pos : List ℕ) (ζ : ℕ) (P1 : ℝ) (nU : ℕ) :
    Obl (estR6 wts r U masses pos ζ P1 nU) :=
  Obl_bind (Obl_loop wts r U masses pos nU _ _) (fun _ => Obl_opn _ _)

lemma Obl_estR5 (pos : List ℕ) (ζ : ℕ) (P1 : ℝ) (nU : ℕ) :
    Obl (estR5 wts r pM U pos ζ P1 nU) :=
  Obl_bind (Obl_opn _ _) (fun masses => Obl_estR6 wts r U masses pos ζ P1 nU)

lemma Obl_estR4 (supp : List ℕ) (ζ : ℕ) (P1 : ℝ) (nU : ℕ) :
    Obl (estR4 wts r pM U supp ζ P1 nU) :=
  Obl_bind (Obl_opn _ _) (fun pos => Obl_estR5 wts r pM U pos ζ P1 nU)

lemma Obl_estR3 (supp : List ℕ) (q : ℝ) (P1 : ℝ) (nU : ℕ) :
    Obl (estR3 wts r pM U e δh supp q P1 nU) :=
  Obl_bind (Obl_opn _ _) (fun ζ => Obl_estR4 wts r pM U supp ζ P1 nU)

lemma Obl_estRq (supp : List ℕ) (wmax wmin : ℝ) (P1 : ℝ) (nU : ℕ) :
    Obl (estRq wts r pM U e δh supp wmax wmin P1 nU) :=
  Obl_bind (Obl_opn _ _) (fun q => Obl_estR3 wts r pM U e δh supp q P1 nU)

lemma Obl_estR2 (supp : List ℕ) (wmax : ℝ) (P1 : ℝ) (nU : ℕ) :
    Obl (estR2 wts r pM U e δh supp wmax P1 nU) :=
  Obl_bind (Obl_foldP _ (fun _ _ => Obl_opn _ _) _ _)
    (fun wmin => Obl_estRq wts r pM U e δh supp wmax wmin P1 nU)

lemma Obl_estRest (supp : List ℕ) (P1 : ℝ) (nU : ℕ) :
    Obl (estRest wts r pM U e δh supp P1 nU) :=
  Obl_bind (Obl_foldP _ (fun _ _ => Obl_opn _ _) _ _)
    (fun wmax => Obl_estR2 wts r pM U e δh supp wmax P1 nU)

lemma Obl_estK3 (supp : List ℕ) (P1 : ℝ) (nU : ℕ) : Obl (estK3 wts r pM U e δh supp P1 nU) :=
  Obl_bind (Obl_opn _ _) (fun _ => Obl_ite _ (Obl_pure _) (Obl_estRest wts r pM U e δh supp P1 nU))

lemma Obl_estK2 (supp : List ℕ) (P1 : ℝ) : Obl (estK2 wts r pM U e δh supp P1) :=
  Obl_bind (Obl_foldP _ (fun _ _ => Obl_opn _ _) _ _)
    (fun nU => Obl_estK3 wts r pM U e δh supp P1 nU)

lemma Obl_estK1 (supp : List ℕ) : Obl (estK1 wts r pM U e δh supp) :=
  Obl_bind (Obl_foldP _ (fun _ _ => Obl_opn _ _) _ _)
    (fun P1 => Obl_estK2 wts r pM U e δh supp P1)

/-! ### Value laws -/

/-- The law of one simulated revenue. -/
noncomputable def sampleLaw (masses : List ℝ) (pos : List ℕ) (nU : ℕ) : PMF ℝ :=
  (catPMF masses).bind fun k => vl (simulate wts r U (pos.getD k 0) nU)

lemma vl_estBody (masses : List ℝ) (pos : List ℕ) (nU : ℕ) (acc : ℝ) :
    vl (estBody wts r U masses pos nU acc) =
      (sampleLaw wts r U masses pos nU).bind fun Y => PMF.pure (acc + Y) := by
  unfold estBody sampleLaw
  rw [vl_bind (Obl_drawCat _) (fun k => Obl_bind (Obl_opn _ _) (fun m =>
    Obl_bind (Obl_simulate wts r U m nU) (fun Y => Obl_opn _ _))), vl_drawCat, PMF.bind_bind]
  congr 1
  funext k
  rw [vl_bind (Obl_opn _ _) (fun m => Obl_bind (Obl_simulate wts r U m nU) (fun Y => Obl_opn _ _)),
    vl_opn, PMF.pure_bind,
    vl_bind (Obl_simulate wts r U _ nU) (fun Y => Obl_opn _ _)]
  simp only [vl_opn]

lemma vl_loop (masses : List ℝ) (pos : List ℕ) (nU : ℕ) : ∀ (l : List ℕ) (a : ℝ),
    vl (foldP l (fun acc _ => estBody wts r U masses pos nU acc) a) =
      sumLaw (sampleLaw wts r U masses pos nU) l.length a
  | [], a => by
    rw [List.length_nil, sumLaw]
    exact vl_pure a
  | x :: l, a => by
    show vl (charge 1 >>= fun _ => (estBody wts r U masses pos nU a >>= fun b' =>
      foldP l (fun acc _ => estBody wts r U masses pos nU acc) b')) = _
    rw [vl_bind (Obl_charge 1) (fun _ => Obl_bind (Obl_estBody wts r U masses pos nU a)
      (fun b' => Obl_loop wts r U masses pos nU l b')), vl_charge, PMF.pure_bind,
      vl_bind (Obl_estBody wts r U masses pos nU a) (fun b' => Obl_loop wts r U masses pos nU l b'),
      vl_estBody, PMF.bind_bind, List.length_cons, sumLaw]
    congr 1
    funext Y
    rw [PMF.pure_bind, vl_loop masses pos nU l (a + Y)]

lemma vl_estR6 (masses : List ℝ) (pos : List ℕ) (ζ : ℕ) (P1 : ℝ) (nU : ℕ) :
    vl (estR6 wts r U masses pos ζ P1 nU) =
      (sumLaw (sampleLaw wts r U masses pos nU) ζ 0).map (fun z => P1 * (z / ζ)) := by
  unfold estR6
  rw [vl_bind (Obl_loop wts r U masses pos nU _ _) (fun _ => Obl_opn _ _), vl_loop,
    List.length_range]
  simp only [vl_opn]
  rfl

end Est


/-! ## Deterministic values computed by the estimator -/

lemma foldl_P1 (pM : ℕ →₀ ℝ) : ∀ (l : List ℕ) (a : ℝ),
    l.foldl (fun acc m => if 1 ≤ m then acc + pM m else acc) a =
      a + ((l.filter (1 ≤ ·)).map pM).sum
  | [], a => by simp
  | m :: l, a => by
    rw [List.foldl_cons, foldl_P1 pM l]
    by_cases hm : 1 ≤ m
    · rw [if_pos hm, List.filter_cons_of_pos (by simpa using hm), List.map_cons, List.sum_cons]
      ring
    · rw [if_neg hm, List.filter_cons_of_neg (by simpa using hm)]

lemma foldl_nU (U : Fin n → ℕ) : ∀ (l : List (Fin n)) (a : ℕ),
    l.foldl (fun acc i => acc + U i) a = a + (l.map U).sum
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, foldl_nU U l, List.map_cons, List.sum_cons]
    ring

lemma nU_eq (U : Fin n → ℕ) : (List.finRange n).foldl (fun acc i => acc + U i) 0 = norm1 U := by
  rw [foldl_nU, zero_add]
  unfold norm1
  rw [← List.sum_toFinset _ (List.nodup_finRange n)]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i
  simp

lemma foldl_max_ge (w : Fin n → ℝ) : ∀ (l : List (Fin n)) (a : ℝ),
    a ≤ l.foldl (fun acc i => max acc (w i)) a ∧
      ∀ j ∈ l, w j ≤ l.foldl (fun acc i => max acc (w i)) a
  | [], a => ⟨le_rfl, by simp⟩
  | x :: l, a => by
    obtain ⟨h1, h2⟩ := foldl_max_ge w l (max a (w x))
    refine ⟨(le_max_left _ _).trans h1, fun j hj => ?_⟩
    rcases List.mem_cons.1 hj with hj | hj
    · rw [hj]
      exact (le_max_right _ _).trans h1
    · exact h2 j hj

lemma foldl_max_le (w : Fin n → ℝ) (c : ℝ) : ∀ (l : List (Fin n)) (a : ℝ), a ≤ c →
    (∀ j ∈ l, w j ≤ c) → l.foldl (fun acc i => max acc (w i)) a ≤ c
  | [], a, ha, _ => ha
  | x :: l, a, ha, hl =>
    foldl_max_le w c l _ (max_le ha (hl x (by simp))) (fun j hj => hl j (by simp [hj]))

lemma foldl_min_le (w : Fin n → ℝ) : ∀ (l : List (Fin n)) (a : ℝ),
    l.foldl (fun acc i => min acc (w i)) a ≤ a ∧
      ∀ j ∈ l, l.foldl (fun acc i => min acc (w i)) a ≤ w j
  | [], a => ⟨le_rfl, by simp⟩
  | x :: l, a => by
    obtain ⟨h1, h2⟩ := foldl_min_le w l (min a (w x))
    refine ⟨h1.trans (min_le_left _ _), fun j hj => ?_⟩
    rcases List.mem_cons.1 hj with hj | hj
    · rw [hj]
      exact h1.trans (min_le_right _ _)
    · exact h2 j hj

lemma foldl_min_ge (w : Fin n → ℝ) (c : ℝ) : ∀ (l : List (Fin n)) (a : ℝ), c ≤ a →
    (∀ j ∈ l, c ≤ w j) → c ≤ l.foldl (fun acc i => min acc (w i)) a
  | [], a, ha, _ => ha
  | x :: l, a, ha, hl =>
    foldl_min_ge w c l _ (le_min ha (hl x (by simp))) (fun j hj => hl j (by simp [hj]))

lemma foldr_min_le' : ∀ (l : List ℝ) (a : ℝ), ∀ x ∈ l, l.foldr min a ≤ x
  | [], _, x, hx => by simp at hx
  | y :: l, a, x, hx => by
    rw [List.foldr_cons]
    rcases List.mem_cons.1 hx with hx | hx
    · rw [hx]
      exact min_le_left _ _
    · exact (min_le_right _ _).trans (foldr_min_le' l a x hx)

lemma foldr_min_pos : ∀ (l : List ℝ) (a : ℝ), 0 < a → (∀ x ∈ l, 0 < x) → 0 < l.foldr min a
  | [], _, ha, _ => ha
  | y :: l, a, ha, hl => by
    rw [List.foldr_cons]
    exact lt_min (hl y (by simp)) (foldr_min_pos l a ha (fun x hx => hl x (by simp [hx])))

lemma wmin_le (wts : Weights n) (j : Fin n) : wts.wmin ≤ wts.w j := by
  unfold Weights.wmin
  exact foldr_min_le' _ _ _ (List.mem_map.2 ⟨j, List.mem_finRange j, rfl⟩)

lemma wmax_pos (wts : Weights n) (hn : 1 ≤ n) (hw : wts.Pos) : 0 < wts.wmax :=
  lt_of_lt_of_le (hw.2 ⟨0, hn⟩) (le_wmax wts ⟨0, hn⟩)

lemma wmin_pos (wts : Weights n) (hn : 1 ≤ n) (hw : wts.Pos) : 0 < wts.wmin := by
  unfold Weights.wmin
  refine foldr_min_pos _ _ (wmax_pos wts hn hw) (fun x hx => ?_)
  obtain ⟨j, _, rfl⟩ := List.mem_map.1 hx
  exact hw.2 j

lemma sum_list_filter_zero (l : List ℕ) (g : ℕ → ℝ) (hg : g 0 = 0) :
    (l.map g).sum = ((l.filter (1 ≤ ·)).map g).sum := by
  induction l with
  | nil => simp
  | cons m l ih =>
    by_cases hm : 1 ≤ m
    · rw [List.filter_cons_of_pos (by simpa using hm), List.map_cons, List.map_cons,
        List.sum_cons, List.sum_cons, ih]
    · have hm0 : m = 0 := by omega
      rw [List.filter_cons_of_neg (by simpa using hm), List.map_cons, List.sum_cons, ih, hm0, hg,
        zero_add]

section Values

variable (wts : Weights n) (r : Fin n → ℝ) (pM : ℕ →₀ ℝ) (U : Fin n → ℕ) (e δh : ℝ)

noncomputable def vSupp : List ℕ := pM.support.sort (· ≤ ·)
noncomputable def vP1 : ℝ :=
  (vSupp pM).foldl (fun acc m => if 1 ≤ m then acc + pM m else acc) 0
def vnU : ℕ := (List.finRange n).foldl (fun acc i => acc + U i) 0
noncomputable def vWmax : ℝ := (List.finRange n).foldl (fun acc i => max acc (wts.w i)) 0
noncomputable def vWmin : ℝ := (List.finRange n).foldl (fun acc i => min acc (wts.w i)) (vWmax wts)
noncomputable def vq : ℝ := vWmin wts / (wts.w0 + n * vWmax wts)
noncomputable def vζ : ℕ := ⌈((vnU U : ℝ) / (vq wts * e)) ^ 2 * Real.log (2 / δh) / 2⌉₊
noncomputable def vPos : List ℕ := (vSupp pM).filter (1 ≤ ·)
noncomputable def vMasses : List ℝ := (vPos pM).map fun m => pM m / vP1 pM

lemma vl_est_triv (h : vP1 pM ≤ 0 ∨ vnU U = 0) :
    vl (estimate wts r pM U e δh) = PMF.pure 0 := by
  rw [estimate_eq, vl_bind_val (f := fun supp => estK1 wts r pM U e δh supp) (VA_opn _ _)
    (Obl_estK1 wts r pM U e δh _)]
  unfold estK1
  rw [vl_bind_val (f := fun P1 => estK2 wts r pM U e δh _ P1)
    (VA_foldP_opn 3 (fun acc m => if 1 ≤ m then acc + pM m else acc) _ 0)
    (Obl_estK2 wts r pM U e δh _ _)]
  unfold estK2
  rw [vl_bind_val (f := fun nU => estK3 wts r pM U e δh _ _ nU)
    (VA_foldP_opn 2 (fun acc i => acc + U i) _ 0) (Obl_estK3 wts r pM U e δh _ _ _)]
  unfold estK3
  rw [vl_bind_val (f := fun triv => if triv = true then (pure 0 : Prog ℝ) else
      estRest wts r pM U e δh _ _ _) (VA_opn _ _)
    (Obl_ite _ (Obl_pure _) (Obl_estRest wts r pM U e δh _ _ _))]
  have h' : decide (vP1 pM ≤ 0 ∨ vnU U = 0) = true := decide_eq_true h
  unfold vP1 vSupp vnU at h'
  rw [h', if_pos rfl]
  exact vl_pure 0

lemma vl_est_main (h : ¬ (vP1 pM ≤ 0 ∨ vnU U = 0)) :
    vl (estimate wts r pM U e δh) =
      (sumLaw (sampleLaw wts r U (vMasses pM) (vPos pM) (vnU U)) (vζ wts U e δh) 0).map
        (fun z => vP1 pM * (z / (vζ wts U e δh))) := by
  rw [estimate_eq, vl_bind_val (f := fun supp => estK1 wts r pM U e δh supp) (VA_opn _ _)
    (Obl_estK1 wts r pM U e δh _)]
  unfold estK1
  rw [vl_bind_val (f := fun P1 => estK2 wts r pM U e δh _ P1)
    (VA_foldP_opn 3 (fun acc m => if 1 ≤ m then acc + pM m else acc) _ 0)
    (Obl_estK2 wts r pM U e δh _ _)]
  unfold estK2
  rw [vl_bind_val (f := fun nU => estK3 wts r pM U e δh _ _ nU)
    (VA_foldP_opn 2 (fun acc i => acc + U i) _ 0) (Obl_estK3 wts r pM U e δh _ _ _)]
  unfold estK3
  rw [vl_bind_val (f := fun triv => if triv = true then (pure 0 : Prog ℝ) else
      estRest wts r pM U e δh _ _ _) (VA_opn _ _)
    (Obl_ite _ (Obl_pure _) (Obl_estRest wts r pM U e δh _ _ _))]
  have h' : decide (vP1 pM ≤ 0 ∨ vnU U = 0) = false := decide_eq_false h
  unfold vP1 vSupp vnU at h'
  rw [h', if_neg (by simp)]
  unfold estRest
  rw [vl_bind_val (f := fun wmax => estR2 wts r pM U e δh _ wmax _ _)
    (VA_foldP_opn 2 (fun acc i => max acc (wts.w i)) _ 0)
    (Obl_estR2 wts r pM U e δh _ _ _ _)]
  unfold estR2
  rw [vl_bind_val (f := fun wmin => estRq wts r pM U e δh _ _ wmin _ _)
    (VA_foldP_opn 2 (fun acc i => min acc (wts.w i)) _ _)
    (Obl_estRq wts r pM U e δh _ _ _ _ _)]
  unfold estRq
  rw [vl_bind_val (f := fun q => estR3 wts r pM U e δh _ q _ _) (VA_opn _ _)
    (Obl_estR3 wts r pM U e δh _ _ _ _)]
  unfold estR3
  rw [vl_bind_val (f := fun ζ => estR4 wts r pM U _ ζ _ _) (VA_opn _ _)
    (Obl_estR4 wts r pM U _ _ _ _)]
  unfold estR4
  rw [vl_bind_val (f := fun pos => estR5 wts r pM U pos _ _ _) (VA_opn _ _)
    (Obl_estR5 wts r pM U _ _ _ _)]
  unfold estR5
  rw [vl_bind_val (f := fun masses => estR6 wts r U masses _ _ _ _) (VA_opn _ _)
    (Obl_estR6 wts r U _ _ _ _ _)]
  rw [vl_estR6]
  rfl

lemma CA_estBody (masses : List ℝ) (pos : List ℕ) (nU : ℕ) (acc : ℝ) :
    CA (estBody wts r U masses pos nU acc)
      ((masses.length + 1) + (1 + ((nU + 1) * (7 * n + 20) + 1))) := by
  unfold estBody
  exact CA_bind (CA_drawCat _) (fun k => CA_bind (CA_opn 1 _) (fun m =>
    CA_bind (CA_simulate wts r U m nU) (fun Y => CA_opn 1 _)))

lemma CA_est :
    CA (estimate wts r pM U e δh)
      ((pM.support.card + 1) + ((vSupp pM).length * (3 + 1) + ((List.finRange n).length * (2 + 1) +
        (2 + ((List.finRange n).length * (2 + 1) + ((List.finRange n).length * (2 + 1) +
          (3 + (10 + ((2 * (vSupp pM).length + 1) + ((2 * (vPos pM).length + 1) +
            ((List.range (vζ wts U e δh)).length *
              (((vMasses pM).length + 1) + (1 + ((vnU U + 1) * (7 * n + 20) + 1)) + 1) +
              3))))))))))) := by
  rw [estimate_eq]
  refine CA_bind_val (CA_opn _ _) (VA_opn _ _) ?_
  unfold estK1
  refine CA_bind_val (CA_foldP _ 3 (fun _ _ => CA_opn _ _) _ _)
    (VA_foldP_opn 3 (fun acc m => if 1 ≤ m then acc + pM m else acc) _ 0) ?_
  unfold estK2
  refine CA_bind_val (CA_foldP _ 2 (fun _ _ => CA_opn _ _) _ _)
    (VA_foldP_opn 2 (fun acc i => acc + U i) _ 0) ?_
  unfold estK3
  refine CA_bind (CA_opn 2 _) (fun triv => CA_ite _ (CA_mono (CA_pure 0) (Nat.zero_le _)) ?_)
  unfold estRest
  refine CA_bind_val (CA_foldP _ 2 (fun _ _ => CA_opn _ _) _ _)
    (VA_foldP_opn 2 (fun acc i => max acc (wts.w i)) _ 0) ?_
  unfold estR2
  refine CA_bind_val (CA_foldP _ 2 (fun _ _ => CA_opn _ _) _ _)
    (VA_foldP_opn 2 (fun acc i => min acc (wts.w i)) _ _) ?_
  unfold estRq
  refine CA_bind_val (CA_opn _ _) (VA_opn _ _) ?_
  unfold estR3
  refine CA_bind_val (CA_opn _ _) (VA_opn _ _) ?_
  unfold estR4
  refine CA_bind_val (CA_opn _ _) (VA_opn _ _) ?_
  unfold estR5
  refine CA_bind_val (CA_opn _ _) (VA_opn _ _) ?_
  unfold estR6
  exact CA_bind (CA_foldP _ _ (fun acc _ => CA_estBody wts r U _ _ _ acc) _ _)
    (fun _ => CA_opn 3 _)

end Values


/-! ## Accuracy and cost of the estimator -/

lemma mean_le (ν : PMF ℝ) (B : ℝ) (hs : ∀ y ∈ ν.support, 0 ≤ y ∧ y ≤ B) :
    ∫ y, y ∂ν.toMeasure ≤ B := by
  have hb := ae_Icc_of_support ν 0 B hs
  have hi : Integrable (fun y : ℝ => y) ν.toMeasure :=
    Integrable.of_mem_Icc 0 B measurable_id.aemeasurable hb
  calc ∫ y, y ∂ν.toMeasure ≤ ∫ _y, B ∂ν.toMeasure :=
        integral_mono_ae hi (integrable_const B) (by
          filter_upwards [hb] with y hy
          exact hy.2)
    _ = B := by simp

section Final

variable (wts : Weights n) (r : Fin n → ℝ) (pM : ℕ →₀ ℝ) (U : Fin n → ℕ) (e δh : ℝ)

lemma pos_toFinset : (vPos pM).toFinset = pM.support.filter (fun m => 1 ≤ m) := by
  ext m
  simp [vPos, vSupp]

lemma pos_nodup : (vPos pM).Nodup := (Finset.sort_nodup _ _).filter _

lemma pos_sum {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ((vPos pM).map g).sum = ∑ m ∈ pM.support.filter (fun m => 1 ≤ m), g m := by
  rw [← pos_toFinset, List.sum_toFinset _ (pos_nodup pM)]

lemma P1_eq : vP1 pM = ∑ m ∈ pM.support.filter (fun m => 1 ≤ m), pM m := by
  unfold vP1
  rw [foldl_P1, zero_add, ← pos_sum]
  rfl

lemma expR_eq (hw : wts.Pos) (hr : ∀ i, 0 ≤ r i) :
    expR wts r pM U =
      ∑ m ∈ pM.support.filter (fun m => 1 ≤ m), pM m * (Fr wts r U m).toReal := by
  unfold expR expX
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← Finset.sum_filter_add_sum_filter_not pM.support (fun m => 1 ≤ m)]
  have h0 : ∑ m ∈ pM.support.filter (fun m => ¬ 1 ≤ m),
      ∑ i, r i * (pM m * expXm wts U m i) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    rw [Finset.mem_filter] at hm
    have hm0 : m = 0 := by omega
    subst hm0
    apply Finset.sum_eq_zero
    intro i _
    have : expXm wts U 0 i = 0 := by
      rw [expXm_eq, demand_zero, EEx_pure]
      simp [Xf]
    rw [this, mul_zero, mul_zero]
  rw [h0, add_zero]
  apply Finset.sum_congr rfl
  intro m _
  rw [Fr_toReal wts hw r hr U m, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma sample_facts (hw : wts.Pos) (hr : ∀ i, 0 ≤ r i) (hpM : IsLaw pM) (hP : 0 < vP1 pM)
    (rs : ℝ) (hrs : ∀ i, 0 < U i → r i ≤ rs) (hrs0 : 0 ≤ rs) :
    (∀ y ∈ (sampleLaw wts r U (vMasses pM) (vPos pM) (vnU U)).support,
      0 ≤ y ∧ y ≤ (norm1 U : ℝ) * rs) ∧
    ∫ y, y ∂(sampleLaw wts r U (vMasses pM) (vPos pM) (vnU U)).toMeasure =
      ∑ m ∈ pM.support.filter (fun m => 1 ≤ m), pM m / vP1 pM * (Fr wts r U m).toReal := by
  have hnU : vnU U = norm1 U := nU_eq U
  have hrange : ∀ y ∈ (sampleLaw wts r U (vMasses pM) (vPos pM) (vnU U)).support,
      0 ≤ y ∧ y ≤ (norm1 U : ℝ) * rs := by
    intro y hy
    unfold sampleLaw at hy
    rw [PMF.mem_support_bind_iff] at hy
    obtain ⟨k, _, hy⟩ := hy
    rw [hnU] at hy
    exact simulate_range wts r U _ rs hrs hr hrs0 y hy
  refine ⟨hrange, ?_⟩
  have hm := mean_ofReal _ _ hrange
  have hmn : ∀ x ∈ vMasses pM, 0 ≤ x := by
    intro x hx
    unfold vMasses at hx
    obtain ⟨m, _, rfl⟩ := List.mem_map.1 hx
    exact div_nonneg (hpM.1 m) hP.le
  have hms : (vMasses pM).sum = 1 := by
    unfold vMasses
    rw [pos_sum pM (fun m => pM m / vP1 pM), ← Finset.sum_div, ← P1_eq, div_self hP.ne']
  have hl : (vMasses pM).length = (vPos pM).length := by
    unfold vMasses
    simp
  have hE : EEx (sampleLaw wts r U (vMasses pM) (vPos pM) (vnU U)) (fun y => ENNReal.ofReal y) =
      ∑ m ∈ pM.support.filter (fun m => 1 ≤ m),
        ENNReal.ofReal (pM m / vP1 pM) * Fr wts r U m := by
    unfold sampleLaw
    rw [EEx_bind]
    simp_rw [hnU, E_simulate wts r hw hr]
    simp_rw [catPMF_apply _ hmn hms]
    rw [tsum_eq_sum (s := Finset.range (vMasses pM).length)]
    · rw [← pos_sum pM (fun m => ENNReal.ofReal (pM m / vP1 pM) * Fr wts r U m), hl]
      apply sum_range_list
      intro k hk
      have hk' : k < (vMasses pM).length := by rw [hl]; exact hk
      rw [List.getD_eq_getElem _ _ hk', List.getD_eq_getElem _ _ hk]
      simp [vMasses]
    · intro k hk
      rw [Finset.mem_range, not_lt] at hk
      rw [List.getD_eq_default _ _ hk, ENNReal.ofReal_zero, zero_mul]
  rw [hm] at hE
  have hnn : 0 ≤ ∫ y, y ∂(sampleLaw wts r U (vMasses pM) (vPos pM) (vnU U)).toMeasure :=
    mean_nonneg _ _ hrange
  have := congrArg ENNReal.toReal hE
  rw [ENNReal.toReal_ofReal hnn, ENNReal.toReal_sum (fun m _ => ENNReal.mul_ne_top
    ENNReal.ofReal_ne_top (Fr_ne_top wts hw r U m))] at this
  rw [this]
  apply Finset.sum_congr rfl
  intro m _
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (div_nonneg (hpM.1 m) hP.le)]

lemma weights_facts (hn : 1 ≤ n) (hw : wts.Pos) :
    (∀ j, wts.w j ≤ vWmax wts) ∧ vWmax wts ≤ wts.wmax ∧ (∀ j, vWmin wts ≤ wts.w j) ∧
      wts.wmin ≤ vWmin wts ∧ 0 < wts.wmin := by
  have h1 : ∀ j, wts.w j ≤ vWmax wts := fun j =>
    (foldl_max_ge wts.w (List.finRange n) 0).2 j (List.mem_finRange j)
  have hWm := wmax_pos wts hn hw
  refine ⟨h1, ?_, fun j => (foldl_min_le wts.w (List.finRange n) _).2 j (List.mem_finRange j),
    ?_, wmin_pos wts hn hw⟩
  · exact foldl_max_le wts.w _ (List.finRange n) 0 hWm.le (fun j _ => le_wmax wts j)
  · refine foldl_min_ge wts.w _ (List.finRange n) _ ?_ (fun j _ => wmin_le wts j)
    exact (wmin_le wts ⟨0, hn⟩).trans (h1 _)

lemma eval_prob (hn : 1 ≤ n) (hw : wts.Pos) (hr : ∀ i, 0 ≤ r i) (hpM : IsLaw pM)
    (he : 0 < e) (hδ : 0 < δh) :
    1 - δh ≤ (((estimate wts r pM U e δh).run 0).toOuterMeasure
      {x | |x.1 - expR wts r pM U| ≤ e * expR wts r pM U}).toReal := by
  have hmap : ((estimate wts r pM U e δh).run 0).toOuterMeasure
      {x | |x.1 - expR wts r pM U| ≤ e * expR wts r pM U} =
      (vl (estimate wts r pM U e δh)).toOuterMeasure
        {y | |y - expR wts r pM U| ≤ e * expR wts r pM U} := by
    unfold vl
    rw [PMF.toOuterMeasure_map_apply]
    rfl
  rw [hmap]
  have hER := expR_eq wts r pM U hw hr
  have hnU : vnU U = norm1 U := nU_eq U
  by_cases htriv : vP1 pM ≤ 0 ∨ vnU U = 0
  · rw [vl_est_triv wts r pM U e δh htriv]
    have hE0 : expR wts r pM U = 0 := by
      rw [hER]
      apply Finset.sum_eq_zero
      intro m hm
      rcases htriv with h | h
      · have hP : vP1 pM = 0 := le_antisymm h (by
          rw [P1_eq]
          exact Finset.sum_nonneg fun m _ => hpM.1 m)
        rw [P1_eq] at hP
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => hpM.1 m)).1 hP m hm
        rw [this, zero_mul]
      · rw [hnU] at h
        have hU : ∀ i, U i = 0 := fun i =>
          Finset.sum_eq_zero_iff.1 (show ∑ i, U i = 0 from h) i (Finset.mem_univ i)
        have hF : Fr wts r U m = 0 := by
          have := Fr_le wts hw r U m
          simp only [hU, Nat.cast_zero, mul_zero, Finset.sum_const_zero,
            nonpos_iff_eq_zero] at this
          exact this
        rw [hF, ENNReal.toReal_zero, mul_zero]
    rw [hE0, (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 ?_, ENNReal.toReal_one]
    · linarith
    · rw [PMF.support_pure, Set.singleton_subset_iff]
      simp
  · have htriv' := htriv
    push_neg at htriv
    obtain ⟨hP, hnU0⟩ := htriv
    by_cases hδ1 : 1 ≤ δh
    · exact le_trans (by linarith) ENNReal.toReal_nonneg
    push_neg at hδ1
    rw [vl_est_main wts r pM U e δh htriv', PMF.toOuterMeasure_map_apply]
    have hne : (Finset.univ.filter fun i => 0 < U i).Nonempty := by
      rw [hnU] at hnU0
      obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (show ∑ i, U i ≠ 0 from hnU0)
      exact ⟨i, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩
    obtain ⟨istar, hist, hmax⟩ := Finset.exists_max_image _ r hne
    have hUi : 0 < U istar := by simpa using hist
    have hrs : ∀ i, 0 < U i → r i ≤ r istar := fun i hi => hmax i (by simpa using hi)
    have hrs0 : 0 ≤ r istar := hr istar
    obtain ⟨hrange, hmean⟩ := sample_facts wts r pM U hw hr hpM hP (r istar) hrs hrs0
    obtain ⟨hW1, hW2, hW3, hW4, hW5⟩ := weights_facts wts hn hw
    have hvmin : 0 < vWmin wts := lt_of_lt_of_le hW5 hW4
    have hvmax : 0 < vWmax wts := lt_of_lt_of_le (hw.2 istar) (hW1 istar)
    have hq : 0 < vq wts := by
      unfold vq
      have : 0 < wts.w0 + n * vWmax wts := by
        have := hw.1
        positivity
      positivity
    have hS0 := wsum_nonneg wts hw U
    have hq_le : vq wts ≤ wts.w istar / (wts.w0 + wts.wsum (inStock U)) := by
      unfold vq
      have hb : 0 < wts.w0 + n * vWmax wts := by
        have := hw.1
        positivity
      have hd : 0 < wts.w0 + wts.wsum (inStock U) := by linarith [hw.1]
      rw [div_le_div_iff₀ hb hd]
      have h1 := hW3 istar
      have h2 := wsum_le_mul wts hw U (vWmax wts) hW1
      have h3 := (hw.2 istar).le
      nlinarith [mul_le_mul_of_nonneg_right h1 (le_of_lt hd), mul_le_mul_of_nonneg_left h2 h3]
    have hsw : ∑ m ∈ pM.support.filter (fun m => 1 ≤ m), pM m / vP1 pM = 1 := by
      rw [← Finset.sum_div, ← P1_eq, div_self hP.ne']
    have hm_low : vq wts * r istar ≤
        ∫ y, y ∂(sampleLaw wts r U (vMasses pM) (vPos pM) (vnU U)).toMeasure := by
      rw [hmean]
      calc vq wts * r istar =
          ∑ m ∈ pM.support.filter (fun m => 1 ≤ m), pM m / vP1 pM * (vq wts * r istar) := by
            rw [← Finset.sum_mul, hsw, one_mul]
        _ ≤ ∑ m ∈ pM.support.filter (fun m => 1 ≤ m), pM m / vP1 pM * (Fr wts r U m).toReal := by
            apply Finset.sum_le_sum
            intro m hm
            apply mul_le_mul_of_nonneg_left _ (div_nonneg (hpM.1 m) hP.le)
            have hm1 : 1 ≤ m := (Finset.mem_filter.1 hm).2
            exact (mul_le_mul_of_nonneg_right hq_le hrs0).trans
              (Fr_lower wts r hw hr U m hm1 istar hUi)
    have hEm : expR wts r pM U = vP1 pM *
        ∫ y, y ∂(sampleLaw wts r U (vMasses pM) (vPos pM) (vnU U)).toMeasure := by
      rw [hER, hmean, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      field_simp
    rw [hEm]
    generalize hν : sampleLaw wts r U (vMasses pM) (vPos pM) (vnU U) = ν at hrange hm_low ⊢
    generalize hmd : ∫ y, y ∂ν.toMeasure = m at hm_low ⊢
    have hmle := mean_le ν _ hrange
    rw [hmd] at hmle
    have hnU' : ((vnU U : ℕ) : ℝ) = (norm1 U : ℝ) := by rw [hnU]
    have hNpos : (0 : ℝ) < norm1 U := by
      rw [hnU] at hnU0
      exact_mod_cast Nat.pos_of_ne_zero hnU0
    by_cases hrz : r istar = 0
    · -- all in-stock prices vanish: the estimate is exactly `0 = E[R(U)]`
      have hm0 : m = 0 := le_antisymm (by rw [hrz, mul_zero] at hmle; exact hmle)
        (by rw [← hmd]; exact mean_nonneg ν _ hrange)
      rw [(PMF.toOuterMeasure_apply_eq_one_iff _ _).2 ?_, ENNReal.toReal_one]
      · linarith
      · intro z hz
        have := sumLaw_support ν _ hrange _ 0 z hz
        rw [hrz, mul_zero, mul_zero, add_zero] at this
        have hz0 : z = 0 := le_antisymm this.2 this.1
        simp [hz0, hm0]
    · have hrpos : 0 < r istar := lt_of_le_of_ne hrs0 (Ne.symm hrz)
      set B := (norm1 U : ℝ) * r istar with hB
      have hBpos : 0 < B := mul_pos hNpos hrpos
      set ζ := vζ wts U e δh with hζ
      set P1 := vP1 pM with hP1
      set s := e * m with hs
      have hL : 0 < Real.log (2 / δh) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
      set X := ((vnU U : ℝ) / (vq wts * e)) ^ 2 * Real.log (2 / δh) / 2 with hX
      have hXpos : 0 < X := by
        rw [hX, hnU']
        have h1 : 0 < (norm1 U : ℝ) / (vq wts * e) := div_pos hNpos (mul_pos hq he)
        exact div_pos (mul_pos (pow_pos h1 2) hL) two_pos
      have hXζ : X ≤ ζ := Nat.le_ceil X
      have hζpos : (0 : ℝ) < ζ := lt_of_lt_of_le hXpos hXζ
      have hs0 : 0 ≤ s := by
        rw [hs]
        exact mul_nonneg he.le (le_trans (by positivity) hm_low)
      have hsq : e * vq wts * r istar ≤ s := by
        rw [hs, mul_assoc]
        exact mul_le_mul_of_nonneg_left hm_low he.le
      have key : Real.log (2 / δh) ≤ 2 * ζ * s ^ 2 / B ^ 2 := by
        have h1 : Real.log (2 / δh) = 2 * X * (e * vq wts * r istar) ^ 2 / B ^ 2 := by
          rw [hX, hB, hnU']
          have : (norm1 U : ℝ) ≠ 0 := hNpos.ne'
          have : vq wts ≠ 0 := hq.ne'
          have : e ≠ 0 := he.ne'
          have : r istar ≠ 0 := hrz
          field_simp
          try ring
        rw [h1]
        have h0 : 0 ≤ e * vq wts * r istar := by positivity
        gcongr
      have hexp : Real.exp (-2 * ζ * s ^ 2 / B ^ 2) ≤ δh / 2 := by
        calc Real.exp (-2 * ζ * s ^ 2 / B ^ 2) ≤ Real.exp (-Real.log (2 / δh)) := by
              apply Real.exp_le_exp.2
              have : -2 * (ζ : ℝ) * s ^ 2 / B ^ 2 = -(2 * ζ * s ^ 2 / B ^ 2) := by ring
              linarith
          _ = δh / 2 := by
              rw [Real.exp_neg, Real.exp_log (div_pos two_pos hδ), inv_div]
      have hsub : ((fun z => P1 * (z / ζ)) ⁻¹' {y | |y - P1 * m| ≤ e * (P1 * m)})ᶜ ⊆
          {z | (ζ : ℝ) * (m + s) ≤ z} ∪ {z | z ≤ (ζ : ℝ) * (m - s)} := by
        intro z hz
        simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_setOf_eq] at hz
        by_contra hc
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hc
        apply hz
        have hlo : m - s < z / ζ := by
          rw [lt_div_iff₀ hζpos]
          linarith [hc.2]
        have hhi : z / ζ < m + s := by
          rw [div_lt_iff₀ hζpos]
          linarith [hc.1]
        have h2 : P1 * s = e * (P1 * m) := by rw [hs]; ring
        have h3 := mul_pos hP (sub_pos.2 hlo)
        have h4 := mul_pos hP (sub_pos.2 hhi)
        rw [abs_le]
        constructor
        · linarith
        · linarith
      have hup := chernoff_upper ν B hBpos hrange ζ s hs0
      have hlow := chernoff_lower ν B hBpos hrange ζ s hs0
      rw [hmd] at hup hlow
      have hbad : (sumLaw ν ζ 0).toOuterMeasure
          ((fun z => P1 * (z / ζ)) ⁻¹' {y | |y - P1 * m| ≤ e * (P1 * m)})ᶜ ≤
          ENNReal.ofReal δh := by
        calc (sumLaw ν ζ 0).toOuterMeasure
              ((fun z => P1 * (z / ζ)) ⁻¹' {y | |y - P1 * m| ≤ e * (P1 * m)})ᶜ
            ≤ (sumLaw ν ζ 0).toOuterMeasure
                ({z | (ζ : ℝ) * (m + s) ≤ z} ∪ {z | z ≤ (ζ : ℝ) * (m - s)}) :=
              MeasureTheory.measure_mono hsub
          _ ≤ (sumLaw ν ζ 0).toOuterMeasure {z | (ζ : ℝ) * (m + s) ≤ z} +
                (sumLaw ν ζ 0).toOuterMeasure {z | z ≤ (ζ : ℝ) * (m - s)} :=
              MeasureTheory.measure_union_le _ _
          _ ≤ ENNReal.ofReal (Real.exp (-2 * ζ * s ^ 2 / B ^ 2)) +
                ENNReal.ofReal (Real.exp (-2 * ζ * s ^ 2 / B ^ 2)) := add_le_add hup hlow
          _ ≤ ENNReal.ofReal (δh / 2) + ENNReal.ofReal (δh / 2) :=
              add_le_add (ENNReal.ofReal_le_ofReal hexp) (ENNReal.ofReal_le_ofReal hexp)
          _ = ENNReal.ofReal δh := by
              rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
              congr 1
              ring
      have hc := outer_add_compl (sumLaw ν ζ 0)
        ((fun z => P1 * (z / ζ)) ⁻¹' {y | |y - P1 * m| ≤ e * (P1 * m)})
      have hne1 : (sumLaw ν ζ 0).toOuterMeasure
          ((fun z => P1 * (z / ζ)) ⁻¹' {y | |y - P1 * m| ≤ e * (P1 * m)}) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top (by rw [← hc]; exact le_self_add)
      have hne2 : (sumLaw ν ζ 0).toOuterMeasure
          ((fun z => P1 * (z / ζ)) ⁻¹' {y | |y - P1 * m| ≤ e * (P1 * m)})ᶜ ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top (by rw [← hc]; exact le_add_self)
      have h1 := congrArg ENNReal.toReal hc
      rw [ENNReal.toReal_add hne1 hne2, ENNReal.toReal_one] at h1
      have h2 := ENNReal.toReal_le_of_le_ofReal hδ.le hbad
      linarith

lemma cost_nat (hn : 1 ≤ n) (x : ℝ × ℕ) (hx : x ∈ ((estimate wts r pM U e δh).run 0).support) :
    x.2 ≤ 40 * (supportSize pM + n * (norm1 U + 1)) +
      vζ wts U e δh * (31 * (supportSize pM + n * (norm1 U + 1))) := by
  have hK := CA_est wts r pM U e δh 0 x hx
  have hnU : vnU U = norm1 U := nU_eq U
  have hsl : (vSupp pM).length = supportSize pM := by
    unfold vSupp supportSize
    simp
  have hcard : pM.support.card = supportSize pM := rfl
  have hpl : (vPos pM).length ≤ supportSize pM := by
    rw [← hsl]
    exact List.length_filter_le _ _
  have hml : (vMasses pM).length = (vPos pM).length := by
    unfold vMasses
    simp
  rw [List.length_range, List.length_finRange, hsl, hml, hnU, hcard, zero_add] at hK
  generalize hSd : supportSize pM = S at hK hpl ⊢
  generalize hpd : (vPos pM).length = p at hK hpl
  generalize hZd : vζ wts U e δh = Z at hK ⊢
  generalize hNd : norm1 U = N at hK ⊢
  have h1 : p + 1 + (1 + ((N + 1) * (7 * n + 20) + 1)) + 1 ≤ 31 * (S + n * (N + 1)) := by
    have := Nat.mul_le_mul_right (N + 1) hn
    nlinarith
  have h2 := Nat.mul_le_mul_left Z h1
  have h3 : n ≤ n * (N + 1) := Nat.le_mul_of_pos_right n (Nat.succ_pos N)
  omega

lemma zeta_bound (hn : 1 ≤ n) (hw : wts.Pos) (ε₀ : ℝ) (hε0 : 0 < ε₀) (hε1 : ε₀ ≤ 1)
    (hεw : ε₀ * wts.w0 / n < wts.wmax) (he : 0 < e) (hδ : 0 < δh) :
    (vζ wts U e δh : ℝ) ≤ 1 + 2 * (((norm1 U : ℝ) + 1) * n * wts.Delta / (ε₀ * e)) ^ 2 *
      (1 + Real.log (max 1 δh⁻¹)) := by
  have hnU : vnU U = norm1 U := nU_eq U
  obtain ⟨hW1, hW2, hW3, hW4, hW5⟩ := weights_facts wts hn hw
  have hvmin : 0 < vWmin wts := lt_of_lt_of_le hW5 hW4
  have hvmax : 0 < vWmax wts := lt_of_lt_of_le (hw.2 ⟨0, hn⟩) (hW1 ⟨0, hn⟩)
  have hWmax : 0 < wts.wmax := lt_of_lt_of_le hvmax hW2
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hw0 := hw.1
  generalize hAd : ((norm1 U : ℝ) + 1) * n * wts.Delta / (ε₀ * e) = A
  generalize hLd : Real.log (max 1 δh⁻¹) = Lm
  have hLm0 : 0 ≤ Lm := by
    rw [← hLd]
    exact Real.log_nonneg (le_max_left _ _)
  have hL2 : Real.log (2 / δh) ≤ 1 + Lm := by
    rw [Real.log_div (by norm_num) hδ.ne']
    have h4 : Real.log δh⁻¹ ≤ Lm := by
      rw [← hLd]
      exact Real.log_le_log (inv_pos.2 hδ) (le_max_right _ _)
    rw [Real.log_inv] at h4
    have h5 := Real.log_two_lt_d9
    linarith
  have hb : 0 < wts.w0 + n * vWmax wts := by positivity
  have hnum : wts.w0 + n * vWmax wts ≤ 2 * n * wts.wmax / ε₀ := by
    have h6 : wts.w0 < n * wts.wmax / ε₀ := by
      rw [lt_div_iff₀ hε0]
      have := (div_lt_iff₀ (lt_of_lt_of_le zero_lt_one hnR)).1 hεw
      linarith
    have h7 : (n : ℝ) * vWmax wts ≤ n * wts.wmax :=
      mul_le_mul_of_nonneg_left hW2 (Nat.cast_nonneg n)
    have h8 : (n : ℝ) * wts.wmax ≤ n * wts.wmax / ε₀ :=
      le_div_self (mul_nonneg (Nat.cast_nonneg n) hWmax.le) hε0 hε1
    have h9 : 2 * n * wts.wmax / ε₀ = n * wts.wmax / ε₀ + n * wts.wmax / ε₀ := by ring
    linarith
  have hq : 0 < vq wts := div_pos hvmin hb
  have hne1 : vWmin wts ≠ 0 := hvmin.ne'
  have hne2 : e ≠ 0 := he.ne'
  have hne3 : wts.w0 + n * vWmax wts ≠ 0 := hb.ne'
  have hne4 : wts.wmin ≠ 0 := hW5.ne'
  have hne5 : ε₀ ≠ 0 := hε0.ne'
  have hratio : (vnU U : ℝ) / (vq wts * e) ≤ 2 * A := by
    rw [hnU]
    have hNn : (0 : ℝ) ≤ norm1 U := Nat.cast_nonneg _
    have e1 : (norm1 U : ℝ) / (vq wts * e) =
        norm1 U * (wts.w0 + n * vWmax wts) / (vWmin wts * e) := by
      unfold vq
      field_simp
      try ring
    rw [e1]
    have hD : 0 ≤ wts.Delta := div_nonneg hWmax.le hW5.le
    calc (norm1 U : ℝ) * (wts.w0 + n * vWmax wts) / (vWmin wts * e)
        ≤ norm1 U * (2 * n * wts.wmax / ε₀) / (vWmin wts * e) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum hNn)
            (mul_pos hvmin he).le
      _ ≤ norm1 U * (2 * n * wts.wmax / ε₀) / (wts.wmin * e) :=
          div_le_div_of_nonneg_left (by positivity) (mul_pos hW5 he)
            (mul_le_mul_of_nonneg_right hW4 he.le)
      _ = 2 * ((norm1 U : ℝ) * n * wts.Delta / (ε₀ * e)) := by
          unfold Weights.Delta
          field_simp
          try ring
      _ ≤ 2 * A := by
          rw [← hAd]
          have h10 : (norm1 U : ℝ) * n * wts.Delta ≤ ((norm1 U : ℝ) + 1) * n * wts.Delta := by
            have := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hD
            linarith
          have h11 := div_le_div_of_nonneg_right h10 (mul_pos hε0 he).le
          linarith
  have hratio0 : 0 ≤ (vnU U : ℝ) / (vq wts * e) :=
    div_nonneg (Nat.cast_nonneg _) (mul_pos hq he).le
  have hsq : ((vnU U : ℝ) / (vq wts * e)) ^ 2 ≤ (2 * A) ^ 2 :=
    pow_le_pow_left₀ hratio0 hratio 2
  have hXle : ((vnU U : ℝ) / (vq wts * e)) ^ 2 * Real.log (2 / δh) / 2 ≤
      2 * A ^ 2 * (1 + Lm) := by
    have h12 := mul_le_mul_of_nonneg_left hL2 (sq_nonneg ((vnU U : ℝ) / (vq wts * e)))
    have h13 := mul_le_mul_of_nonneg_right hsq (by linarith : (0 : ℝ) ≤ 1 + Lm)
    linarith
  unfold vζ
  rcases le_or_gt (((vnU U : ℝ) / (vq wts * e)) ^ 2 * Real.log (2 / δh) / 2) 0 with h | h
  · rw [Nat.ceil_eq_zero.2 h, Nat.cast_zero]
    have : 0 ≤ 2 * A ^ 2 * (1 + Lm) := by positivity
    linarith
  · have := Nat.ceil_lt_add_one h.le
    linarith

lemma eval_cost (hn : 1 ≤ n) (hw : wts.Pos) (ε₀ : ℝ) (hε0 : 0 < ε₀) (hε1 : ε₀ ≤ 1)
    (hεw : ε₀ * wts.w0 / n < wts.wmax) (he : 0 < e) (hδ : 0 < δh) :
    ∀ x ∈ ((estimate wts r pM U e δh).run 0).support,
      (x.2 : ℝ) ≤ 200 * (supportSize pM + n * (norm1 U + 1)) *
        (1 + ((norm1 U + 1) * n * wts.Delta / (ε₀ * e)) ^ 2) *
          (1 + Real.log (max 1 δh⁻¹)) := by
  intro x hx
  have hK2 := cost_nat wts r pM U e δh hn x hx
  have hZ := zeta_bound wts U e δh hn hw ε₀ hε0 hε1 hεw he hδ
  have hKR : (x.2 : ℝ) ≤ 40 * ((supportSize pM : ℝ) + n * ((norm1 U : ℝ) + 1)) +
      (vζ wts U e δh : ℝ) * (31 * ((supportSize pM : ℝ) + n * ((norm1 U : ℝ) + 1))) := by
    exact_mod_cast hK2
  generalize hAd : ((norm1 U : ℝ) + 1) * n * wts.Delta / (ε₀ * e) = A at hZ ⊢
  generalize hLd : Real.log (max 1 δh⁻¹) = Lm at hZ ⊢
  have hLm0 : 0 ≤ Lm := by
    rw [← hLd]
    exact Real.log_nonneg (le_max_left _ _)
  generalize hZd : (vζ wts U e δh : ℝ) = Z at hZ hKR
  generalize hN0d : (supportSize pM : ℝ) + n * ((norm1 U : ℝ) + 1) = N0 at hKR ⊢
  have hN0 : 0 ≤ N0 := by
    rw [← hN0d]
    positivity
  have hZ0 : 0 ≤ Z := by
    rw [← hZd]
    exact Nat.cast_nonneg _
  have hQ1 : 1 ≤ (1 + A ^ 2) * (1 + Lm) := by nlinarith [sq_nonneg A]
  have hQ2 : A ^ 2 * (1 + Lm) ≤ (1 + A ^ 2) * (1 + Lm) := by nlinarith [sq_nonneg A]
  have h1 : Z * (31 * N0) ≤ (1 + 2 * A ^ 2 * (1 + Lm)) * (31 * N0) :=
    mul_le_mul_of_nonneg_right hZ (by linarith)
  have h2 := mul_le_mul_of_nonneg_left hQ1 hN0
  have h3 := mul_le_mul_of_nonneg_left hQ2 hN0
  have e1 : 200 * N0 * (1 + A ^ 2) * (1 + Lm) = 200 * (N0 * ((1 + A ^ 2) * (1 + Lm))) := by ring
  have e2 : (1 + 2 * A ^ 2 * (1 + Lm)) * (31 * N0) = 31 * N0 + 62 * (N0 * (A ^ 2 * (1 + Lm))) := by
    ring
  rw [e1]
  rw [e2] at h1
  linarith

end Final

theorem eval_main : ∃ c₁ : ℝ, 0 < c₁ ∧
    ∀ (n : ℕ) (wts : Weights n), 1 ≤ n → wts.Pos → ∀ r : Fin n → ℝ, (∀ i, 0 ≤ r i) →
    ∀ pM : ℕ →₀ ℝ, IsLaw pM → ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ ≤ 1 → ε₀ * wts.w0 / n < wts.wmax →
    ∀ (U : Fin n → ℕ) (e δh : ℝ), 0 < e → 0 < δh →
      1 - δh ≤ (((estimate wts r pM U e δh).run 0).toOuterMeasure
          {x | |x.1 - expR wts r pM U| ≤ e * expR wts r pM U}).toReal ∧
      ∀ x ∈ ((estimate wts r pM U e δh).run 0).support,
        (x.2 : ℝ) ≤ c₁ * (supportSize pM + n * (norm1 U + 1)) *
          (1 + ((norm1 U + 1) * n * wts.Delta / (ε₀ * e)) ^ 2) *
            (1 + Real.log (max 1 δh⁻¹)) := by
  refine ⟨200, by norm_num, ?_⟩
  intro n wts hn hw r hr pM hpM ε₀ hε0 hε1 hεw U e δh he hδ
  exact ⟨eval_prob wts r pM U e δh hn hw hr hpM he hδ,
    eval_cost wts r pM U e δh hn hw ε₀ hε0 hε1 hεw he hδ⟩

end Aux_MNLS0

open MNLStability in
theorem solution : ∃ c₁ : ℝ, 0 < c₁ ∧
    ∀ (n : ℕ) (wts : Weights n), 1 ≤ n → wts.Pos → ∀ r : Fin n → ℝ, (∀ i, 0 ≤ r i) →
    ∀ pM : ℕ →₀ ℝ, IsLaw pM → ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ ≤ 1 → ε₀ * wts.w0 / n < wts.wmax →
    ∀ (U : Fin n → ℕ) (e δh : ℝ), 0 < e → 0 < δh →
      1 - δh ≤ (((estimate wts r pM U e δh).run 0).toOuterMeasure
          {x | |x.1 - expR wts r pM U| ≤ e * expR wts r pM U}).toReal ∧
      ∀ x ∈ ((estimate wts r pM U e δh).run 0).support,
        (x.2 : ℝ) ≤ c₁ * (supportSize pM + n * (norm1 U + 1)) *
          (1 + ((norm1 U + 1) * n * wts.Delta / (ε₀ * e)) ^ 2) *
            (1 + Real.log (max 1 δh⁻¹)) :=
  Aux_MNLS0.eval_main
