-- Prove2me | solution 1 for GlobalTheory.RestrMeas.IsRestrGroup.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:55:08.656793+00:00
-- url     : https://prove2.me/submissions/17bffe77-df4b-4e6d-abf7-128599ae13d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ExistsFinsetOfEventually
import Theorems.Thm_GlobalTheory_RestrMeas_cyl_self
import Theorems.Thm_GlobalTheory_RestrMeas_exists_extend_one
import Theorems.Thm_GlobalTheory_RestrMeas_mem_levelAway

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RestrMeas
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal NNReal
variable {X W V : Type} {Ya : W → Type} {Yf : V → Type} [Group X] [∀ w, Group (Ya w)] [∀ v, Group (Yf v)]
  [TopologicalSpace X] [∀ w, TopologicalSpace (Ya w)] [∀ v, TopologicalSpace (Yf v)]
variable {pa : ∀ w, X →* Ya w} {pf : ∀ v, X →* Yf v} {K K' : ∀ v, Subgroup (Yf v)}
variable [Fintype W] [MeasurableSpace X] [∀ w, MeasurableSpace (Ya w)] [∀ v, MeasurableSpace (Yf v)]
variable {μa : ∀ w, Measure (Ya w)} {μf : ∀ v, Measure (Yf v)} {μ μ' : Measure X}
variable [BorelSpace X] [∀ w, BorelSpace (Ya w)] [∀ v, BorelSpace (Yf v)] [IsTopologicalGroup X]
variable [LocallyCompactSpace X] [SecondCountableTopology X] [∀ w, IsTopologicalGroup (Ya w)]
  [∀ w, LocallyCompactSpace (Ya w)] [∀ w, T2Space (Ya w)]
variable [∀ w, SecondCountableTopology (Ya w)] [∀ v, IsTopologicalGroup (Yf v)] [∀ v, LocallyCompactSpace (Yf v)]
  [∀ v, SecondCountableTopology (Yf v)]
omit [LocallyCompactSpace X] [SecondCountableTopology X] [∀ w, T2Space (Ya w)]
namespace GlobalTheory.RestrMeas
namespace IsRestrGroup
theorem _root_.solution (h : IsRestrGroup pa pf K) (μa : ∀ w, Measure (Ya w)) (μf : ∀ v, Measure (Yf v))
    [∀ w, (μa w).IsHaarMeasure] [∀ v, (μf v).IsHaarMeasure] (ν : Measure X) [ν.IsHaarMeasure] (S : Finset V) :
    ∃ c : ℝ≥0∞, ∀ (A : ∀ w, Set (Ya w)) (B : ∀ v, Set (Yf v)), (∀ w, MeasurableSet (A w)) →
      (∀ v ∈ S, MeasurableSet (B v)) →
      ν (cyl (fun w => pa w) (fun v => pf v) (fun v => (K v : Set (Yf v))) S A B) =
        c * ((∏ w, μa w (A w)) * ∏ v ∈ S, μf v (B v)) := by
  classical
  let π : X →* (∀ w, Ya w) × ∀ v : S, Yf v := (MonoidHom.pi pa).prod (MonoidHom.pi fun v : S => pf v)
  have hπ : Measurable π := ((continuous_pi h.continuous_pa).prodMk
    (continuous_pi fun v : S => h.continuous_pf v)).measurable
  let m : Measure ((∀ w, Ya w) × ∀ v : S, Yf v) := (ν.restrict (levelAway pf K S)).map π
  have hm : ∀ s, MeasurableSet s → m s = ν (π ⁻¹' s ∩ levelAway pf K S) := fun s hs => by
    rw [Measure.map_apply hπ hs, Measure.restrict_apply (hπ hs)]
  have hc : ∀ (A : ∀ w, Set (Ya w)) (B : ∀ v, Set (Yf v)), (∀ w, MeasurableSet (A w)) →
      (∀ v ∈ S, MeasurableSet (B v)) → m (univ.pi A ×ˢ univ.pi fun v : S => B v) =
      ν (cyl (fun w => pa w) (fun v => pf v) (fun v => (K v : Set (Yf v))) S A B) := fun A B hA hB => by
    rw [hm _ ((MeasurableSet.univ_pi hA).prod (MeasurableSet.univ_pi fun v => hB v v.2))]
    refine congrArg ν (Set.ext fun t => ?_)
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ_pi, mem_cyl, SetLike.mem_coe, mem_levelAway, and_assoc]
    exact and_congr_right fun _ => and_congr_left fun _ => Subtype.forall
  haveI : m.IsMulLeftInvariant := (forall_measure_preimage_mul_iff m).1 fun y s hs => by
    obtain ⟨z, hz1, hz2⟩ := exists_extend_one (j := fun v : S => v.1) Subtype.val_injective y.2
    have hz3 : ∀ v ∉ S, z v ∈ K v := fun v hv => by rw [hz2 v (by simpa using hv)]; exact one_mem _
    obtain ⟨x, hx1, hx2⟩ := h.exists_eq y.1 z (eventually_of_finset S hz3)
    have hx : π x = y := Prod.ext (funext hx1) (funext fun v => (hx2 v).trans (hz1 v))
    have hxU : x ∈ levelAway pf K S := mem_levelAway.2 fun v hv => hx2 v ▸ hz3 v hv
    rw [hm _ (measurable_const_mul y hs), hm _ hs, ← measure_preimage_mul ν x (π ⁻¹' s ∩ _)]
    refine congrArg ν (Set.ext fun t => ?_)
    simp [hx, Subgroup.mul_mem_cancel_left _ hxU]
  let C : ∀ w, TopologicalSpace.PositiveCompacts (Ya w) := fun w => Classical.arbitrary _
  haveI : IsFiniteMeasureOnCompacts m := ⟨fun s hs => by
    refine measure_lt_top_of_isCompact_of_isMulLeftInvariant
      (univ.pi (fun w => interior (C w)) ×ˢ univ.pi fun v : S => (K v : Set (Yf v)))
      ((isOpen_set_pi finite_univ fun w _ => isOpen_interior).prod (isOpen_set_pi finite_univ fun v _ => h.isOpen_K v))
      ((univ_pi_nonempty_iff.2 fun w => (C w).interior_nonempty).prod
        (univ_pi_nonempty_iff.2 fun v => ⟨1, one_mem _⟩)) ?_ hs
    rw [hc _ (fun v => K v) (fun w => isOpen_interior.measurableSet) fun v _ => (h.isOpen_K v).measurableSet, cyl_self]
    refine ne_top_of_le_ne_top (h.isCompact_level (fun w => C w) fun w => (C w).isCompact).measure_lt_top.ne
      (measure_mono fun x hx => ⟨fun w => interior_subset (hx.1 w), hx.2⟩)⟩
  refine ⟨haarScalarFactor m ((Measure.pi μa).prod (Measure.pi fun v : S => μf v)), fun A B hA hB => ?_⟩
  rw [← hc A B hA hB]
  conv_lhs => rw [isMulLeftInvariant_eq_smul m ((Measure.pi μa).prod (Measure.pi fun v : S => μf v))]
  rw [Measure.smul_apply, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul,
    Finset.prod_coe_sort S fun v => μf v (B v)]
end IsRestrGroup
end GlobalTheory.RestrMeas
