-- Prove2me | solution 1 for LovaszSchrijver.Defect.valid_N_of_deletion_contraction
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T16:48:32.391018+00:00
-- url     : https://prove2.me/submissions/72e74902-6ef9-4268-93a9-eb3f812ca1ae

import Definitions.Def_LovaszSchrijver_Defect_Index
import Mathlib.Tactic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_LovaszSchrijver_IntegerHull_Basic
import Definitions.Def_LovaszSchrijver_IntegerHull_MatrixCone
open Matrix Pointwise

set_option autoImplicit false

namespace LS32d53bf7

open LovaszSchrijver.IntegerHull

variable {ι : Type}

/-! ### cone API -/

theorem subset_cone (S : Set (Option ι → ℝ)) : S ⊆ cone S := fun _ hx => by
  unfold cone
  exact Submodule.subset_span hx

theorem cone_induction {S : Set (Option ι → ℝ)} {P : (Option ι → ℝ) → Prop}
    (hS : ∀ x ∈ S, P x) (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ c : ℝ, 0 ≤ c → ∀ x, P x → P (c • x)) {x : Option ι → ℝ} (hx : x ∈ cone S) :
    P x := by
  unfold cone at hx
  have hx' : x ∈ PointedCone.hull ℝ S := hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy => exact hS y hy
  | zero => exact h0
  | add y z _ _ hy hz => exact hadd y z hy hz
  | smul a y _ hy => exact hsmul a a.2 y hy

theorem zero_mem_cone (S : Set (Option ι → ℝ)) : (0 : Option ι → ℝ) ∈ cone S := by
  unfold cone
  exact Submodule.zero_mem (PointedCone.hull ℝ S)

theorem add_mem_cone {S : Set (Option ι → ℝ)} {x y : Option ι → ℝ} (hx : x ∈ cone S)
    (hy : y ∈ cone S) : x + y ∈ cone S := by
  unfold cone at *
  exact Submodule.add_mem (PointedCone.hull ℝ S) hx hy

theorem smul_mem_cone {S : Set (Option ι → ℝ)} {c : ℝ} (hc : 0 ≤ c) {x : Option ι → ℝ}
    (hx : x ∈ cone S) : c • x ∈ cone S := by
  unfold cone at *
  exact Submodule.smul_mem (PointedCone.hull ℝ S) (⟨c, hc⟩ : {c : ℝ // 0 ≤ c}) hx

theorem cone_mono {S T : Set (Option ι → ℝ)} (h : S ⊆ T) {x : Option ι → ℝ}
    (hx : x ∈ cone S) : x ∈ cone T :=
  cone_induction (fun _ hy => subset_cone T (h hy)) (zero_mem_cone T)
    (fun _ _ => add_mem_cone) (fun _ hc _ => smul_mem_cone hc) hx

/-! ### bounds on Q -/

theorem Q_bounds {x : Option ι → ℝ} (hx : x ∈ (Q : Set (Option ι → ℝ))) :
    0 ≤ x none ∧ ∀ i, 0 ≤ x (some i) ∧ x (some i) ≤ x none := by
  have hx' : x ∈ cone {x : Option ι → ℝ | IsZeroOne x ∧ x none = 1} := hx
  refine cone_induction (P := fun x => 0 ≤ x none ∧ ∀ i, 0 ≤ x (some i) ∧ x (some i) ≤ x none)
    ?_ ?_ ?_ ?_ hx'
  · rintro p ⟨hp, hp0⟩
    refine ⟨by rw [hp0]; norm_num, fun i => ?_⟩
    rcases hp (some i) with h | h <;> rw [h, hp0] <;> norm_num
  · exact ⟨le_refl _, fun i => ⟨le_refl _, le_refl _⟩⟩
  · rintro x y ⟨hx0, hx⟩ ⟨hy0, hy⟩
    refine ⟨by simp only [Pi.add_apply]; linarith, fun i => ?_⟩
    have := hx i
    have := hy i
    simp only [Pi.add_apply]
    constructor <;> linarith [(hx i).1, (hx i).2, (hy i).1, (hy i).2]
  · rintro c hc x ⟨hx0, hx⟩
    refine ⟨by simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hc hx0, fun i => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    exact ⟨mul_nonneg hc (hx i).1, mul_le_mul_of_nonneg_left (hx i).2 hc⟩

/-! ### bipolar -/

theorem bipolar [Fintype ι] [DecidableEq ι] {C : Set (Option ι → ℝ)}
    (h0 : (0 : Option ι → ℝ) ∈ C)
    (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C) (hsmul : ∀ c : ℝ, 0 ≤ c → ∀ x ∈ C, c • x ∈ C)
    (hcl : IsClosed C) {z : Option ι → ℝ} (hz : ∀ u ∈ dualCone C, 0 ≤ u ⬝ᵥ z) : z ∈ C := by
  by_contra hzC
  have hconv : Convex ℝ C := by
    intro x hx y hy a b ha hb _
    exact hadd _ (hsmul a ha x hx) _ (hsmul b hb y hy)
  obtain ⟨f, u, hf, hfz⟩ := geometric_hahn_banach_closed_point hconv hcl hzC
  have hu : 0 < u := by
    have := hf 0 h0
    simpa using this
  have hle : ∀ a ∈ C, f a ≤ 0 := by
    intro a ha
    by_contra h
    have h : 0 < f a := not_le.1 h
    have hpos : 0 ≤ u / f a + 1 := by positivity
    have := hf ((u / f a + 1) • a) (hsmul _ hpos a ha)
    rw [map_smul, smul_eq_mul] at this
    have h2 : (u / f a + 1) * f a = u + f a := by field_simp
    linarith
  have hfw : ∀ x, f x = (fun j => f (fun k => if j = k then (1:ℝ) else 0)) ⬝ᵥ x := by
    intro x
    have := LinearMap.pi_apply_eq_sum_univ (f : (Option ι → ℝ) →ₗ[ℝ] ℝ) x
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [this]
    simp only [dotProduct, smul_eq_mul]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  set w : Option ι → ℝ := fun j => f (fun k => if j = k then (1:ℝ) else 0) with hw
  have hmem : -w ∈ dualCone C := by
    intro a ha
    rw [neg_dotProduct, ← hfw]
    linarith [hle a ha]
  have := hz (-w) hmem
  rw [neg_dotProduct, ← hfw] at this
  linarith

/-! ### closedness of a sum of two bounded closed sets -/

theorem add_closed [Fintype ι] {A B : Set (Option ι → ℝ)} (hA : IsClosed A) (hB : IsClosed B)
    (hAb : ∀ a ∈ A, ‖a‖ ≤ a none) (hBb : ∀ b ∈ B, ‖b‖ ≤ b none) : IsClosed (A + B) := by
  refine isClosed_of_closure_subset (fun z hz => ?_)
  set R : ℝ := z none + 1 with hR
  have hU : IsOpen {y : Option ι → ℝ | y none < R} :=
    isOpen_lt (continuous_apply none) continuous_const
  have hzU : z ∈ {y : Option ι → ℝ | y none < R} := by
    show z none < R
    linarith
  have h1 : z ∈ closure ({y : Option ι → ℝ | y none < R} ∩ (A + B)) :=
    hU.inter_closure ⟨hzU, hz⟩
  have hP : IsCompact ((A ∩ Metric.closedBall 0 R) + (B ∩ Metric.closedBall 0 R)) :=
    ((isCompact_closedBall 0 R).inter_left hA).add ((isCompact_closedBall 0 R).inter_left hB)
  have hsub : {y : Option ι → ℝ | y none < R} ∩ (A + B) ⊆
      (A ∩ Metric.closedBall 0 R) + (B ∩ Metric.closedBall 0 R) := by
    rintro y ⟨hy, a, ha, b, hb, rfl⟩
    have h0a : 0 ≤ a none := (norm_nonneg a).trans (hAb a ha)
    have h0b : 0 ≤ b none := (norm_nonneg b).trans (hBb b hb)
    have hy' : a none + b none < R := by simpa using hy
    exact ⟨a, ⟨ha, by rw [mem_closedBall_zero_iff]; linarith [hAb a ha]⟩, b,
      ⟨hb, by rw [mem_closedBall_zero_iff]; linarith [hBb b hb]⟩, rfl⟩
  have h2 : z ∈ closure ((A ∩ Metric.closedBall 0 R) + (B ∩ Metric.closedBall 0 R)) :=
    closure_mono hsub h1
  rw [hP.isClosed.closure_eq] at h2
  obtain ⟨a, ha, b, hb, rfl⟩ := h2
  exact ⟨a, ha.1, b, hb.1, rfl⟩

/-! ### the recursively defined cones -/

def Cl {ι : Type} (K : Set (Option ι → ℝ)) : List ι → Set (Option ι → ℝ)
  | [] => K
  | i :: l => (Cl K l ∩ H i) + (Cl K l ∩ G i)

theorem norm_le_of_Q [Fintype ι] {a : Option ι → ℝ} (ha : a ∈ (Q : Set (Option ι → ℝ))) :
    ‖a‖ ≤ a none := by
  obtain ⟨h0, hb⟩ := Q_bounds ha
  refine (pi_norm_le_iff_of_nonneg h0).2 (fun j => ?_)
  rw [Real.norm_eq_abs]
  cases j with
  | none => exact le_of_eq (abs_of_nonneg h0)
  | some i => rw [abs_of_nonneg (hb i).1]; exact (hb i).2

theorem Cl_props [Fintype ι] {K : Set (Option ι → ℝ)} (hK : IsConvexCone K) (hKc : IsClosed K)
    (hKQ : K ⊆ Q) (l : List ι) :
    IsClosed (Cl K l) ∧ Cl K l ⊆ K ∧ (0 : Option ι → ℝ) ∈ Cl K l ∧
      (∀ x ∈ Cl K l, ∀ y ∈ Cl K l, x + y ∈ Cl K l) ∧
      ∀ c : ℝ, 0 ≤ c → ∀ x ∈ Cl K l, c • x ∈ Cl K l := by
  induction l with
  | nil =>
    obtain ⟨⟨x0, hx0⟩, hadd, hsmul⟩ := hK
    refine ⟨hKc, fun x hx => hx, ?_, hadd, hsmul⟩
    have := hsmul 0 le_rfl x0 hx0
    have h00 : (0 : Option ι → ℝ) ∈ K := by simpa using this
    exact h00
  | cons i l ih =>
    obtain ⟨hcl, hsub, h0, hadd, hsmul⟩ := ih
    have hH : IsClosed (H i : Set (Option ι → ℝ)) :=
      isClosed_eq (continuous_apply (some i)) continuous_const
    have hG : IsClosed (G i : Set (Option ι → ℝ)) :=
      isClosed_eq (continuous_apply (some i)) (continuous_apply none)
    have hA : IsClosed (Cl K l ∩ H i) := hcl.inter hH
    have hB : IsClosed (Cl K l ∩ G i) := hcl.inter hG
    have hAb : ∀ a ∈ Cl K l ∩ H i, ‖a‖ ≤ a none := fun a ha => norm_le_of_Q (hKQ (hsub ha.1))
    have hBb : ∀ a ∈ Cl K l ∩ G i, ‖a‖ ≤ a none := fun a ha => norm_le_of_Q (hKQ (hsub ha.1))
    refine ⟨add_closed hA hB hAb hBb, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      exact hK.2.1 a (hsub ha.1) b (hsub hb.1)
    · exact ⟨0, ⟨h0, by simp [H]⟩, 0, ⟨h0, by simp [G]⟩, by simp⟩
    · rintro _ ⟨a, ha, b, hb, rfl⟩ _ ⟨a', ha', b', hb', rfl⟩
      refine ⟨a + a', ⟨hadd a ha.1 a' ha'.1, ?_⟩, b + b', ⟨hadd b hb.1 b' hb'.1, ?_⟩, (add_add_add_comm a b a' b').symm⟩
      · have h1 : a (some i) = 0 := ha.2
        have h2 : a' (some i) = 0 := ha'.2
        show (a + a') (some i) = 0
        simp [h1, h2]
      · have h1 : b (some i) = b none := hb.2
        have h2 : b' (some i) = b' none := hb'.2
        show (b + b') (some i) = (b + b') none
        simp [h1, h2]
    · rintro c hc _ ⟨a, ha, b, hb, rfl⟩
      refine ⟨c • a, ⟨hsmul c hc a ha.1, ?_⟩, c • b, ⟨hsmul c hc b hb.1, ?_⟩, by rw [smul_add]⟩
      · have h1 : a (some i) = 0 := ha.2
        show (c • a) (some i) = 0
        simp [h1]
      · have h1 : b (some i) = b none := hb.2
        show (c • b) (some i) = (c • b) none
        simp [h1]

/-! ### faces of a generated cone -/

theorem cone_face {S : Set (Option ι → ℝ)} (φ : (Option ι → ℝ) → ℝ)
    (hadd : ∀ x y, φ (x + y) = φ x + φ y) (hsmul : ∀ (c : ℝ) x, φ (c • x) = c * φ x)
    (h0 : φ 0 = 0)
    (hφ : ∀ p ∈ S, 0 ≤ φ p) {a : Option ι → ℝ} (ha : a ∈ cone S) :
    0 ≤ φ a ∧ (φ a = 0 → a ∈ cone (S ∩ {p | φ p = 0})) := by
  refine cone_induction (P := fun a => 0 ≤ φ a ∧ (φ a = 0 → a ∈ cone (S ∩ {p | φ p = 0})))
    ?_ ?_ ?_ ?_ ha
  · intro p hp
    exact ⟨hφ p hp, fun h => subset_cone _ ⟨hp, h⟩⟩
  · exact ⟨by rw [h0], fun _ => zero_mem_cone _⟩
  · rintro x y ⟨hx0, hx⟩ ⟨hy0, hy⟩
    refine ⟨by rw [hadd]; linarith, fun h => ?_⟩
    rw [hadd] at h
    exact add_mem_cone (hx (by linarith)) (hy (by linarith))
  · rintro c hc x ⟨hx0, hx⟩
    refine ⟨by rw [hsmul]; exact mul_nonneg hc hx0, fun h => ?_⟩
    rw [hsmul] at h
    rcases mul_eq_zero.1 h with h | h
    · subst h
      simpa using zero_mem_cone _
    · exact smul_mem_cone hc (hx h)

theorem K_sub_cone {K : Set (Option ι → ℝ)} (hK : IsConvexCone K) (hKQ : K ⊆ Q) :
    K ⊆ cone (K ∩ Fbar (∅ : Finset ι)) := by
  intro x hx
  obtain ⟨h0, hb⟩ := Q_bounds (hKQ hx)
  rcases h0.eq_or_lt with h | h
  · have hx0 : x = 0 := by
      funext j
      cases j with
      | none => exact h.symm
      | some i => 
        have := hb i
        show x (some i) = 0
        linarith [this.1, this.2]
    rw [hx0]
    exact zero_mem_cone _
  · have hxe : x = x none • ((x none)⁻¹ • x) := by
      rw [smul_smul, mul_inv_cancel₀ h.ne', one_smul]
    rw [hxe]
    refine smul_mem_cone h.le (subset_cone _ ⟨hK.2.2 _ (inv_nonneg.2 h.le) x hx, ?_, ?_, ?_⟩)
    · simp [h.ne']
    · intro i
      have := hb i
      simp only [Pi.smul_apply, smul_eq_mul]
      refine ⟨mul_nonneg (inv_nonneg.2 h.le) this.1, ?_⟩
      rw [inv_mul_le_iff₀ h]
      linarith [this.2]
    · intro i hi
      simp at hi

theorem Cl_sub_cone [Fintype ι] [DecidableEq ι] {K : Set (Option ι → ℝ)} (hK : IsConvexCone K)
    (hKQ : K ⊆ Q) (l : List ι) : Cl K l ⊆ cone (K ∩ Fbar l.toFinset) := by
  induction l with
  | nil => simpa [Cl] using K_sub_cone hK hKQ
  | cons i l ih =>
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have ha' := ih ha.1
    have hb' := ih hb.1
    refine add_mem_cone ?_ ?_
    · have := (cone_face (fun p => p (some i)) (fun x y => rfl) (fun c x => rfl) rfl
        (fun p hp => (hp.2.2.1 i).1) ha').2
        (by simpa [H] using ha.2)
      refine cone_mono ?_ this
      rintro p ⟨⟨hpK, hp0, hpc, hpT⟩, hpi⟩
      have hpi' : p (some i) = 0 := hpi
      refine ⟨hpK, hp0, hpc, ?_⟩
      intro j hj
      rw [List.toFinset_cons, Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact Or.inl hpi'
      · exact hpT j hj
    · have := (cone_face (fun p => p none - p (some i))
        (fun x y => by simp only [Pi.add_apply]; ring)
        (fun c x => by simp only [Pi.smul_apply, smul_eq_mul]; ring) (by simp)
        (fun p hp => by
          have h1 := (hp.2.2.1 i).2
          have h2 := hp.2.1
          show 0 ≤ p none - p (some i)
          linarith) hb').2
        (by
          have h1 : b (some i) = b none := hb.2
          show b none - b (some i) = 0
          rw [h1]; ring)
      refine cone_mono ?_ this
      rintro p ⟨⟨hpK, hp0, hpc, hpT⟩, hpi⟩
      have hpi' : p none - p (some i) = 0 := hpi
      refine ⟨hpK, hp0, hpc, ?_⟩
      intro j hj
      rw [List.toFinset_cons, Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · right; linarith
      · exact hpT j hj

/-! ### the upper bound -/

theorem Niter_sub_Cl [Fintype ι] [DecidableEq ι] {K : Set (Option ι → ℝ)} (hK : IsConvexCone K)
    (hKc : IsClosed K) (hKQ : K ⊆ Q) (l : List ι) : Niter l.length K ⊆ Cl K l := by
  induction l with
  | nil => exact fun x hx => hx
  | cons i l ih =>
    intro x hx
    have hx' : x ∈ N1 (Niter l.length K) := hx
    obtain ⟨Y, ⟨hsymm, hdiag, hdual⟩, rfl⟩ := hx'
    obtain ⟨hcl, -, h0, hadd, hsmul⟩ := Cl_props hK hKc hKQ l
    have hei : (Pi.single (some i) (1:ℝ) : Option ι → ℝ) ∈ dualCone (Q : Set (Option ι → ℝ)) := by
      intro x hx
      have := (Q_bounds hx).2 i
      simp only [single_dotProduct]
      linarith [this.1]
    have he0i : (Pi.single none (1:ℝ) - Pi.single (some i) (1:ℝ) : Option ι → ℝ) ∈
        dualCone (Q : Set (Option ι → ℝ)) := by
      intro x hx
      have := (Q_bounds hx).2 i
      simp only [sub_dotProduct, single_dotProduct]
      linarith [this.2]
    have hdual' : ∀ u ∈ dualCone (Cl K l), ∀ v ∈ dualCone (Q : Set (Option ι → ℝ)),
        0 ≤ u ⬝ᵥ (Y *ᵥ v) := fun u hu v hv =>
      hdual u (fun x hx => hu x (ih hx)) v hv
    have hB : Y *ᵥ Pi.single (some i) (1:ℝ) ∈ Cl K l :=
      bipolar h0 hadd hsmul hcl (fun u hu => hdual' u hu _ hei)
    have hA : Y *ᵥ (Pi.single none (1:ℝ) - Pi.single (some i) (1:ℝ)) ∈ Cl K l :=
      bipolar h0 hadd hsmul hcl (fun u hu => hdual' u hu _ he0i)
    have hdi : Y (some i) (some i) = Y none (some i) := hdiag i
    have hs : Y (some i) none = Y none (some i) := by
      have := hsymm.apply none (some i)
      exact this
    refine ⟨Y *ᵥ (Pi.single none (1:ℝ) - Pi.single (some i) (1:ℝ)), ⟨hA, ?_⟩,
      Y *ᵥ Pi.single (some i) (1:ℝ), ⟨hB, ?_⟩, ?_⟩
    · show (Y *ᵥ (Pi.single none (1:ℝ) - Pi.single (some i) (1:ℝ))) (some i) = 0
      simp [Matrix.mulVec_sub, hs, hdi]
    · show (Y *ᵥ Pi.single (some i) (1:ℝ)) (some i) = (Y *ᵥ Pi.single (some i) (1:ℝ)) none
      simp [hdi]
    · show _ + _ = _
      rw [← Matrix.mulVec_add]
      congr 1
      abel

/-! ### the lower bound -/

theorem hull01_sub_Niter [Fintype ι] [DecidableEq ι] {K : Set (Option ι → ℝ)}
    (hK : IsConvexCone K) (hKQ : K ⊆ Q) (t : ℕ) : hull01 K ⊆ Niter t K := by
  induction t with
  | zero =>
    intro x hx
    have hx' : x ∈ cone {x : Option ι → ℝ | x ∈ K ∧ IsZeroOne x} := hx
    refine cone_induction (P := fun x => x ∈ K) (fun y hy => hy.1) ?_ (fun x y hx hy => hK.2.1 x hx y hy)
      (fun c hc x hx => hK.2.2 c hc x hx) hx'
    obtain ⟨x0, hx0⟩ := hK.1
    have := hK.2.2 0 le_rfl x0 hx0
    simpa using this
  | succ t ih =>
    intro x hx
    have hx' : x ∈ cone {x : Option ι → ℝ | x ∈ K ∧ IsZeroOne x} := hx
    show x ∈ N (Niter t K) Q
    refine cone_induction (P := fun x => x ∈ N (Niter t K) (Q : Set (Option ι → ℝ))) ?_ ?_ ?_ ?_ hx'
    · rintro p ⟨hpK, hp01⟩
      have hpQ := Q_bounds (hKQ hpK)
      have hpN : p ∈ Niter t K := ih (subset_cone _ ⟨hpK, hp01⟩)
      have hxx : ∀ j, p j * p none = p j := by
        intro j
        rcases hp01 none with h0 | h0
        · have : p j = 0 := by
            cases j with
            | none => exact h0
            | some i => linarith [(hpQ.2 i).1, (hpQ.2 i).2]
          rw [this]; ring
        · rw [h0]; ring
      refine ⟨Matrix.vecMulVec p p, ⟨?_, ?_, ?_⟩, ?_⟩
      · ext i j
        simp [Matrix.vecMulVec, mul_comm]
      · intro i
        simp only [Matrix.vecMulVec_apply]
        rcases hp01 (some i) with h | h
        · rw [h]; ring
        · have := hxx (some i)
          rw [h] at this ⊢
          linarith
      · intro u hu v hv
        have hvv : Matrix.vecMulVec p p *ᵥ v = (p ⬝ᵥ v) • p := by
          ext k
          simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
            Finset.sum_mul]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        rw [hvv, dotProduct_smul, smul_eq_mul]
        have h1 : 0 ≤ v ⬝ᵥ p := hv p (hKQ hpK)
        have h2 : 0 ≤ u ⬝ᵥ p := hu p hpN
        rw [dotProduct_comm p v]
        exact mul_nonneg h1 h2
      · funext j
        simp [Matrix.vecMulVec_apply, hxx j]
    · exact ⟨0, ⟨by simp [Matrix.IsSymm], by simp, by simp⟩, Matrix.zero_mulVec _⟩
    · rintro x y ⟨Y1, ⟨s1, d1, u1⟩, e1⟩ ⟨Y2, ⟨s2, d2, u2⟩, e2⟩
      refine ⟨Y1 + Y2, ⟨s1.add s2, fun i => ?_, fun u hu v hv => ?_⟩, ?_⟩
      · simp [Matrix.add_apply, d1 i, d2 i]
      · rw [Matrix.add_mulVec, dotProduct_add]
        exact add_nonneg (u1 u hu v hv) (u2 u hu v hv)
      · rw [Matrix.add_mulVec, e1, e2]
    · rintro c hc x ⟨Y, ⟨s, d, u⟩, e⟩
      refine ⟨c • Y, ⟨s.smul c, fun i => ?_, fun w hw v hv => ?_⟩, ?_⟩
      · simp [d i]
      · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
        exact mul_nonneg hc (u w hw v hv)
      · rw [Matrix.smul_mulVec, e]

end LS32d53bf7


namespace LSProof
open Finset Matrix LovaszSchrijver.IntegerHull LS32d53bf7
variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma zero_mem {K : Set (Option ι → ℝ)} (hK : IsConvexCone K) : (0:Option ι→ℝ)∈K := by
  obtain ⟨x,hx⟩ := hK.1
  simpa using hK.2.2 0 le_rfl x hx

lemma Q_dual_unit (j : Option ι) : (Pi.single j 1 : Option ι→ℝ)∈dualCone Q := by
  intro x hx
  rw [single_dotProduct,one_mul]
  cases j with
  | none => exact (Q_bounds hx).1
  | some i => exact ((Q_bounds hx).2 i).1

lemma Q_dual_diff (i : ι) : (Pi.single none 1-Pi.single (some i) 1 : Option ι→ℝ)∈dualCone Q := by
  intro x hx
  rw [sub_dotProduct,single_dotProduct,single_dotProduct,one_mul,one_mul]
  exact sub_nonneg.mpr ((Q_bounds hx).2 i).2

lemma cube_dual (w : Option ι→ℝ) (hw0 : 0≤w none)
    (hw : ∀ i,0≤w (some i) ∧ w (some i)≤w none)
    (v : Option ι→ℝ) (hv : v∈dualCone Q) : 0≤w ⬝ᵥ v := by
  classical
  let b : Option ι→ℝ := fun j=>match j with | none=>1 | some i=>if v (some i)<0 then 1 else 0
  have hb : b∈Q := by
    apply subset_cone
    refine ⟨?_,rfl⟩
    intro j
    cases j with
    | none => exact Or.inr rfl
    | some i => dsimp [b];split_ifs <;> simp
  have hval : 0≤v none+∑ i:ι,if v (some i)<0 then v (some i) else 0 := by
    simpa [dotProduct,Fintype.sum_option,b,mul_ite] using hv b hb
  have hs : w none*(∑ i:ι,if v (some i)<0 then v (some i) else 0)≤∑ i:ι,w (some i)*v (some i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    split_ifs with hi
    · exact mul_le_mul_of_nonpos_right (hw i).2 hi.le
    · simpa using mul_nonneg (hw i).1 (le_of_not_gt hi)
  have ht := mul_nonneg hw0 hval
  simp only [dotProduct,Fintype.sum_option]
  nlinarith

lemma columns {K : Set (Option ι→ℝ)} (hK : IsConvexCone K) (hKc : IsClosed K)
    (Y : Matrix (Option ι) (Option ι) ℝ) (hs : Y.IsSymm)
    (hd : ∀ i:ι,Y (some i) (some i)=Y none (some i)) :
    Y∈M K Q ↔ (∀ j:Option ι,Y*ᵥPi.single j 1∈K) ∧
      ∀ i:ι,Y*ᵥPi.single none 1-Y*ᵥPi.single (some i) 1∈K := by
  constructor
  · intro hY
    constructor
    · intro j
      exact bipolar (zero_mem hK) hK.2.1 hK.2.2 hKc (fun u hu=>hY.2.2 u hu _ (Q_dual_unit j))
    · intro i
      rw [←Matrix.mulVec_sub]
      exact bipolar (zero_mem hK) hK.2.1 hK.2.2 hKc (fun u hu=>hY.2.2 u hu _ (Q_dual_diff i))
  · rintro ⟨hcol,hdiff⟩
    refine ⟨hs,hd,?_⟩
    intro u hu v hv
    have he (j:Option ι) : (u ᵥ* Y) j=u ⬝ᵥ (Y*ᵥPi.single j 1) := by
      simp [Matrix.vecMul,Matrix.mulVec_single,Matrix.col]
      rfl
    have hw0 : 0≤(u ᵥ* Y) none := by rw [he];exact hu _ (hcol none)
    have hw : ∀ i,0≤(u ᵥ* Y) (some i) ∧ (u ᵥ* Y) (some i)≤(u ᵥ* Y) none := by
      intro i
      rw [he,he]
      refine ⟨hu _ (hcol _),?_⟩
      have hh := hu _ (hdiff i)
      rw [dotProduct_sub] at hh
      linarith
    rw [Matrix.dotProduct_mulVec]
    exact cube_dual _ hw0 hw v hv

lemma M_swap {K L : Set (Option ι→ℝ)} {Y : Matrix (Option ι) (Option ι) ℝ} (hY:Y∈M K L) : Y∈M L K := by
  refine ⟨hY.1,hY.2.1,?_⟩
  intro u hu v hv
  have he := Matrix.dotProduct_transpose_mulVec Y u v
  rw [hY.1] at he
  rw [he]
  exact hY.2.2 v hv u hu

lemma M_mono {K L K' L' : Set (Option ι→ℝ)} (hK:K⊆K') (hL:L⊆L') : M K L⊆M K' L' := by
  intro Y hY
  exact ⟨hY.1,hY.2.1,fun u hu v hv=>hY.2.2 u (fun x hx=>hu x (hK hx)) v (fun x hx=>hv x (hL hx))⟩

lemma inter_cone {K L : Set (Option ι→ℝ)} (hK:IsConvexCone K) (hL:IsConvexCone L) : IsConvexCone (K∩L) :=
  ⟨⟨0,zero_mem hK,zero_mem hL⟩,fun x hx y hy=>⟨hK.2.1 x hx.1 y hy.1,hL.2.1 x hx.2 y hy.2⟩,
    fun c hc x hx=>⟨hK.2.2 c hc x hx.1,hL.2.2 c hc x hx.2⟩⟩

lemma intersection {K L : Set (Option ι→ℝ)} (hK:IsConvexCone K) (hL:IsConvexCone L)
    (hKc:IsClosed K) (hLc:IsClosed L) (hKQ:K⊆Q) (hLQ:L⊆Q) :
    N (K∩L) (K∩L)⊆N K L ∧ N K L⊆N (K∩L) Q := by
  constructor
  · rintro x ⟨Y,hY,hx⟩
    exact ⟨Y,M_mono Set.inter_subset_left Set.inter_subset_right hY,hx⟩
  · rintro x ⟨Y,hY,hx⟩
    have hYK := (columns hK hKc Y hY.1 hY.2.1).mp (M_mono (fun _ h=>h) hLQ hY)
    have hYL := (columns hL hLc Y hY.1 hY.2.1).mp (M_mono (fun _ h=>h) hKQ (M_swap hY))
    refine ⟨Y,(columns (inter_cone hK hL) (hKc.inter hLc) Y hY.1 hY.2.1).mpr ?_,hx⟩
    exact ⟨fun j=>⟨hYK.1 j,hYL.1 j⟩,fun i=>⟨hYK.2 i,hYL.2 i⟩⟩

end LSProof

namespace LSProof
open Finset Matrix LovaszSchrijver.IntegerHull LS32d53bf7
variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma hull_positive {K L : Set (Option ι→ℝ)} (hKQ : K⊆Q) : hull01 (K∩L)⊆Nplus K L := by
  intro x hx
  apply cone_induction (P:=fun x=>x∈Nplus K L) ?_ ?_ ?_ ?_ hx
  · rintro p ⟨⟨hpK,hpL⟩,hp01⟩
    have hpQ := Q_bounds (hKQ hpK)
    have hxx : ∀ j,p j*p none=p j := by
      intro j
      rcases hp01 none with h0|h0
      · have hj : p j=0 := by
          cases j with
          | none => exact h0
          | some i => linarith [(hpQ.2 i).1,(hpQ.2 i).2]
        rw [hj];ring
      · rw [h0];ring
    refine ⟨Matrix.vecMulVec p p,⟨⟨?_,?_,?_⟩,?_⟩,?_⟩
    · ext i j
      simp [Matrix.vecMulVec,mul_comm]
    · intro i
      simp only [Matrix.vecMulVec_apply]
      rcases hp01 (some i) with h|h
      · rw [h];ring
      · have hh := hxx (some i)
        rw [h] at hh ⊢
        linarith
    · intro u hu v hv
      have hvv : Matrix.vecMulVec p p*ᵥv=(p ⬝ᵥ v) • p := by
        ext k
        simp only [Matrix.mulVec,dotProduct,Matrix.vecMulVec_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_mul]
        exact Finset.sum_congr rfl (fun j _=>by ring)
      rw [hvv,dotProduct_smul,smul_eq_mul,dotProduct_comm p v]
      exact mul_nonneg (hv p hpL) (hu p hpK)
    · simpa using Matrix.posSemidef_vecMulVec_self_star p
    · funext j
      simp [Matrix.vecMulVec_apply,hxx j]
  · refine ⟨0,⟨⟨by simp [Matrix.IsSymm],by simp,by simp⟩,?_⟩,Matrix.zero_mulVec _⟩
    exact Matrix.PosSemidef.zero
  · rintro x y ⟨Y1,⟨⟨s1,d1,u1⟩,ps1⟩,e1⟩ ⟨Y2,⟨⟨s2,d2,u2⟩,ps2⟩,e2⟩
    refine ⟨Y1+Y2,⟨⟨s1.add s2,fun i=>?_,fun u hu v hv=>?_⟩,ps1.add ps2⟩,?_⟩
    · simp [Matrix.add_apply,d1 i,d2 i]
    · rw [Matrix.add_mulVec,dotProduct_add]
      exact add_nonneg (u1 u hu v hv) (u2 u hu v hv)
    · rw [Matrix.add_mulVec,e1,e2]
  · rintro c hc x ⟨Y,⟨⟨s,d,u⟩,ps⟩,e⟩
    refine ⟨c•Y,⟨⟨s.smul c,fun i=>?_,fun w hw v hv=>?_⟩,ps.smul hc⟩,?_⟩
    · simp [d i]
    · rw [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
      exact mul_nonneg hc (u w hw v hv)
    · rw [Matrix.smul_mulVec,e]

lemma inclusions {K L : Set (Option ι→ℝ)} (hK:IsConvexCone K) (hL:IsConvexCone L)
    (hKc:IsClosed K) (hLc:IsClosed L) (hKQ:K⊆Q) (hLQ:L⊆Q) :
    hull01 (K∩L)⊆Nplus K L ∧ Nplus K L⊆N K L ∧ N K L⊆K∩L := by
  refine ⟨hull_positive hKQ,?_,?_⟩
  · rintro x ⟨Y,hY,hx⟩
    exact ⟨Y,hY.1,hx⟩
  · rintro x ⟨Y,hY,rfl⟩
    have hYK := (columns hK hKc Y hY.1 hY.2.1).mp (M_mono (fun _ h=>h) hLQ hY)
    have hYL := (columns hL hLc Y hY.1 hY.2.1).mp (M_mono (fun _ h=>h) hKQ (M_swap hY))
    exact ⟨hYK.1 none,hYL.1 none⟩

end LSProof

namespace LSDProof
open Finset Matrix LovaszSchrijver.Defect
variable {V : Type} [Fintype V] [DecidableEq V]

lemma FR_bounds (G:SimpleGraph V) (hG:∀v,∃w,G.Adj v w) (v:V)
    {x:Option V→ℝ} (hx:x∈FR G) : 0≤x none ∧ ∀i,0≤x (some i) ∧ x (some i)≤x none := by
  have hi (i:V) : x (some i)≤x none := by
    obtain ⟨j,hj⟩ := hG i
    linarith [hx.1 j,hx.2 i j hj]
  exact ⟨(hx.1 v).trans (hi v),fun i=>⟨hx.1 i,hi i⟩⟩

lemma valid_hom {K:Set (Option V→ℝ)} (hK:IsConvexCone K) (a:V→ℝ) (b:ℝ)
    (hv:Valid {x|hom x∈K} a b) (w:Option V→ℝ) (hw:w∈K)
    (h0:0≤w none) (hb:∀i,0≤w (some i) ∧ w (some i)≤w none) :
    a ⬝ᵥ (fun i=>w (some i))≤b*w none := by
  rcases h0.eq_or_lt with he|he
  · have hz : ∀i,w (some i)=0 := fun i=>by linarith [(hb i).1,(hb i).2]
    simp [dotProduct,hz,he.symm]
  · let z : V→ℝ := fun i=>w (some i)/w none
    have hh : hom z=(w none)⁻¹ • w := by
      funext j
      cases j with
      | none => simp [hom,he.ne']
      | some i => simp [hom,z,div_eq_mul_inv,mul_comm]
    have hhK : hom z∈K := by
      rw [hh]
      exact hK.2.2 _ (inv_nonneg.mpr he.le) _ hw
    have h := hv z hhK
    have hdot : a ⬝ᵥ z=(a ⬝ᵥ (fun i=>w (some i)))/w none := by
      simp [dotProduct,z,Finset.sum_div,mul_div_assoc]
    rw [hdot] at h
    exact (div_le_iff₀ he).mp h

lemma valid_split (G:SimpleGraph V) [DecidableRel G.Adj] (hG:∀v,∃w,G.Adj v w)
    (K:Set (Option V→ℝ)) (hK:IsConvexCone K) (hKc:IsClosed K) (hKFR:K⊆FR G)
    (a:V→ℝ) (b:ℝ) (v:V)
    (hdel:Valid {x|hom x∈K} (deletion a v) b)
    (hcon:Valid {x|hom x∈K} (contraction G a v) (b-a v)) :
    Valid {x|hom x∈N1 K} a b := by
  intro x hx
  obtain ⟨Y,hY,hx⟩ := hx
  have hcols := (LSProof.columns hK hKc Y hY.1 hY.2.1).mp hY
  let A := Y*ᵥPi.single none (1:ℝ)-Y*ᵥPi.single (some v) (1:ℝ)
  let B := Y*ᵥPi.single (some v) (1:ℝ)
  have hAK : A∈K := hcols.2 v
  have hBK : B∈K := hcols.1 (some v)
  have hA := FR_bounds G hG v (hKFR hAK)
  have hB := FR_bounds G hG v (hKFR hBK)
  have hsum : A+B=hom x := by dsimp [A,B];rw [sub_add_cancel,hx]
  have hAv : A (some v)=0 := by
    dsimp [A]
    simp [hY.2.1 v,hY.1.apply none (some v)]
  have hBv : B (some v)=B none := by dsimp [B];simp [hY.2.1 v]
  have hBn (j:V) (hj:G.Adj v j) : B (some j)=0 := by
    have hh := (hKFR hBK).2 v j hj
    linarith [(hB.2 j).1]
  have hda : (deletion a v) ⬝ᵥ (fun i=>A (some i))=a ⬝ᵥ (fun i=>A (some i)) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi:i=v
    · subst i;simp [deletion,hAv]
    · simp [deletion,hi]
  have hdb : a ⬝ᵥ (fun i=>B (some i))=
      (contraction G a v) ⬝ᵥ (fun i=>B (some i))+a v*B none := by
    have he (i:V) : a i*B (some i)=(contraction G a v) i*B (some i)+
        (if i=v then a v*B none else 0) := by
      by_cases hi:i=v
      · subst i;simp [contraction,hBv]
      · by_cases hn:G.Adj v i
        · simp [contraction,hi,hn,hBn i hn]
        · simp [contraction,hi,hn]
    simp only [dotProduct]
    rw [Finset.sum_congr rfl (fun i _=>he i),Finset.sum_add_distrib]
    simp
  have ha := valid_hom hK (deletion a v) b hdel A hAK hA.1 hA.2
  have hb := valid_hom hK (contraction G a v) (b-a v) hcon B hBK hB.1 hB.2
  rw [hda] at ha
  have hz : A none+B none=1 := by simpa [hom] using congrFun hsum none
  have hdx : a ⬝ᵥ x=a ⬝ᵥ (fun i=>A (some i))+a ⬝ᵥ (fun i=>B (some i)) := by
    rw [←dotProduct_add]
    congr 1
    funext i
    exact (congrFun hsum (some i)).symm
  rw [hdx,hdb]
  have hbz := congrArg (fun t:ℝ=>b*t) hz
  nlinarith [hbz]

end LSDProof

namespace LSDProof
open Finset Matrix LovaszSchrijver.Defect
variable {V : Type} [Fintype V] [DecidableEq V]

lemma of_columns {K:Set (Option V→ℝ)} (Y:Matrix (Option V) (Option V) ℝ) (hs:Y.IsSymm)
    (hd:∀i:V,Y (some i) (some i)=Y none (some i))
    (hcol:∀j:Option V,Y*ᵥPi.single j 1∈K)
    (hdiff:∀i:V,Y*ᵥPi.single none 1-Y*ᵥPi.single (some i) 1∈K) : Y∈M K Q := by
  refine ⟨hs,hd,?_⟩
  intro u hu v hv
  have he (j:Option V) : (u ᵥ* Y) j=u ⬝ᵥ (Y*ᵥPi.single j 1) := by
    simp [Matrix.vecMul,Matrix.mulVec_single,Matrix.col]
    rfl
  have hw0 : 0≤(u ᵥ* Y) none := by rw [he];exact hu _ (hcol none)
  have hw : ∀i,0≤(u ᵥ* Y) (some i) ∧ (u ᵥ* Y) (some i)≤(u ᵥ* Y) none := by
    intro i
    rw [he,he]
    refine ⟨hu _ (hcol _),?_⟩
    have hh := hu _ (hdiff i)
    rw [dotProduct_sub] at hh
    linarith
  rw [Matrix.dotProduct_mulVec]
  exact LSProof.cube_dual _ hw0 hw v hv

lemma N_smul {K L:Set (Option V→ℝ)} {x:Option V→ℝ} (hx:x∈N K L) (c:ℝ) (hc:0≤c) : c•x∈N K L := by
  obtain ⟨Y,⟨s,d,u⟩,e⟩ := hx
  refine ⟨c•Y,⟨s.smul c,fun i=>?_,fun w hw v hv=>?_⟩,?_⟩
  · simp [d i]
  · rw [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
    exact mul_nonneg hc (u w hw v hv)
  · rw [Matrix.smul_mulVec,e]

lemma iter_smul (G:SimpleGraph V) (n:ℕ) {x:Option V→ℝ} (hx:x∈Niter n (FR G))
    (c:ℝ) (hc:0≤c) : c•x∈Niter n (FR G) := by
  cases n with
  | zero =>
    refine ⟨fun i=>mul_nonneg hc (hx.1 i),?_⟩
    intro i j hij
    have hh := mul_le_mul_of_nonneg_left (hx.2 i j hij) hc
    simpa [mul_add] using hh
  | succ n => exact N_smul hx c hc

lemma binary_iter (G:SimpleGraph V) (p:Option V→ℝ) (hp:p∈FR G) (hp0:p none=1)
    (hp01:∀j,p j=0 ∨ p j=1) (n:ℕ) : p∈Niter n (FR G) := by
  induction n with
  | zero => exact hp
  | succ n ih =>
    have hpQ : p∈Q := LS32d53bf7.subset_cone _ ⟨hp01,hp0⟩
    refine ⟨Matrix.vecMulVec p p,⟨?_,?_,?_⟩,?_⟩
    · ext i j;simp [Matrix.vecMulVec,mul_comm]
    · intro i
      simp only [Matrix.vecMulVec_apply,hp0,one_mul]
      rcases hp01 (some i) with h|h <;> rw [h] <;> norm_num
    · intro u hu v hv
      have hvv : Matrix.vecMulVec p p*ᵥv=(p ⬝ᵥ v) • p := by
        ext k
        simp only [Matrix.mulVec,dotProduct,Matrix.vecMulVec_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_mul]
        exact Finset.sum_congr rfl (fun j _=>by ring)
      rw [hvv,dotProduct_smul,smul_eq_mul,dotProduct_comm p v]
      exact mul_nonneg (hv p hpQ) (hu p ih)
    · funext j;simp [Matrix.vecMulVec_apply,hp0]

lemma unit_iter (G:SimpleGraph V) (i:V) (n:ℕ) : hom (Pi.single i (1:ℝ))∈Niter n (FR G) := by
  apply binary_iter G _ ?_ rfl ?_ n
  · refine ⟨fun j=>by simp [hom,Pi.single_apply];split_ifs <;> norm_num,?_⟩
    intro j k hjk
    by_cases hj:j=i
    · subst j
      have hk:k≠i := hjk.ne.symm
      simp [hom,Pi.single_apply,hk]
    · by_cases hk:k=i
      · subst k;simp [hom,Pi.single_apply,hj]
      · simp [hom,Pi.single_apply,hj,hk]
  · intro j
    cases j with
    | none => exact Or.inr rfl
    | some j => by_cases hj:j=i <;> simp [hom,Pi.single_apply,hj]

noncomputable def liftDiag (x:V→ℝ) : Matrix (Option V) (Option V) ℝ := fun i j=>
  match i,j with
  | none,none=>1
  | none,some j=>x j
  | some i,none=>x i
  | some i,some j=>if i=j then x i else 0

lemma cube_iter (G:SimpleGraph V) (n:ℕ) (x:V→ℝ)
    (hx:∀i,0≤x i ∧ x i≤1/((n:ℝ)+2)) : hom x∈Niter n (FR G) := by
  induction n generalizing x with
  | zero =>
    refine ⟨fun i=>(hx i).1,?_⟩
    intro i j hij
    change x i+x j≤1
    have hi := (hx i).2
    have hj := (hx j).2
    norm_num at hi hj
    linarith
  | succ n ih =>
    have hn : (0:ℝ)≤n := Nat.cast_nonneg n
    have hp : 0<(n:ℝ)+2 := by positivity
    have hp' : 0<(n:ℝ)+3 := by positivity
    have hx' : ∀i,0≤x i ∧ x i≤1/((n:ℝ)+3) := by simpa only [Nat.cast_add,Nat.cast_one,add_assoc,show (1:ℝ)+2=3 by norm_num] using hx
    let Y := liftDiag x
    have hsym : Y.IsSymm := by
      ext i j
      cases i <;> cases j <;> simp [Y,liftDiag,Matrix.transpose_apply]
      rename_i i j
      by_cases hij:i=j
      · subst j;simp
      · simp [hij,Ne.symm hij]
    have hdiag : ∀i:V,Y (some i) (some i)=Y none (some i) := by intro i;simp [Y,liftDiag]
    have hnone : Y*ᵥPi.single none 1=hom x := by ext j;cases j <;> simp [Y,liftDiag,hom]
    have hsome (i:V) : Y*ᵥPi.single (some i) 1=x i • hom (Pi.single i 1) := by
      ext j
      cases j with
      | none => simp [Y,liftDiag,hom]
      | some j => by_cases hj:j=i <;> simp [Y,liftDiag,hom,Pi.single_apply,hj]
    have hcol : ∀j:Option V,Y*ᵥPi.single j 1∈Niter n (FR G) := by
      intro j
      cases j with
      | none =>
        rw [hnone]
        apply ih
        intro i
        refine ⟨(hx' i).1,(hx' i).2.trans ?_⟩
        exact one_div_le_one_div_of_le hp (by linarith)
      | some i =>
        rw [hsome]
        exact iter_smul G n (unit_iter G i n) _ (hx' i).1
    have hdiff : ∀i:V,Y*ᵥPi.single none 1-Y*ᵥPi.single (some i) 1∈Niter n (FR G) := by
      intro i
      have hxi : x i<1 := by
        have hh := (le_div_iff₀ hp').mp (hx' i).2
        nlinarith [(hx' i).1]
      have hden : 0<1-x i := by linarith
      let z : V→ℝ := fun j=>if j=i then 0 else x j/(1-x i)
      have hz : ∀j,0≤z j ∧ z j≤1/((n:ℝ)+2) := by
        intro j
        by_cases hj:j=i
        · simp [z,hj,hp.le]
        · simp only [z,if_neg hj]
          refine ⟨div_nonneg (hx' j).1 hden.le,?_⟩
          apply (div_le_div_iff₀ hden hp).mpr
          have hi := (hx' i).2
          have hj' := (hx' j).2
          have hmul := mul_le_mul_of_nonneg_right hj' hp.le
          have he : (1/((n:ℝ)+3))*((n:ℝ)+2)+1/((n:ℝ)+3)=1 := by field_simp;ring
          nlinarith
      have he : Y*ᵥPi.single none 1-Y*ᵥPi.single (some i) 1=(1-x i) • hom z := by
        rw [hnone,hsome]
        ext j
        cases j with
        | none => simp [hom]
        | some j =>
          by_cases hj:j=i
          · subst j;simp [hom,z]
          · simp [hom,z,Pi.single_apply,hj]
            field_simp [ne_of_gt hden]
      rw [he]
      exact iter_smul G n (ih z hz) _ hden.le
    exact ⟨Y,of_columns Y hsym hdiag hcol hdiff,hnone⟩

end LSDProof

namespace LovaszSchrijver.Defect

theorem _root_.solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (K : Set (Option V → ℝ)) (hK : IsConvexCone K) (hKc : IsClosed K) (hKFR : K ⊆ FR G)
    (a : V → ℝ) (b : ℝ) (v : V)
    (hdel : Valid {x | hom x ∈ K} (deletion a v) b)
    (hcon : Valid {x | hom x ∈ K} (contraction G a v) (b - a v)) :
    Valid {x | hom x ∈ N1 K} a b := by
  exact LSDProof.valid_split G hG K hK hKc hKFR a b v hdel hcon

end LovaszSchrijver.Defect
