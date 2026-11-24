-- Prove2me | solution 1 for GlobalTheory.AdLat.RootNear.finite_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:28:47.10214+00:00
-- url     : https://prove2.me/submissions/87d7d04a-9499-48f4-ae4e-3285e0370fb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdeleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsAdeleRingTensorEquivInfiniteProdFiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsRootNear
import Theorems.Thm_GlobalTheory_AdLat_RootNear_finite_root
import Theorems.Thm_GlobalTheory_T_isOpen_nsmul_adelicCompletionOfVectorSet


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
noncomputable section
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.RootNear
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.AdLat.RootNear
theorem _root_.solution (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (hP : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) :
    letI : TopologicalSpace (RA F E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (RA F E)
    ∀ V ∈ 𝓝 (1 : RA F E), ∀ᶠ u in 𝓝 (1 : RA F E), u * sg (FiniteAdeleRing (𝓞 F) F) c u = 1 →
      ∃ x ∈ V, ∃ y ∈ V, x * y = 1 ∧ x = u * sg (FiniteAdeleRing (𝓞 F) F) c x := by
  letI : TopologicalSpace (RA F E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (RA F E)
  have : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (RA F E) := ⟨rfl⟩
  have : ContinuousAdd (RA F E) := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) _
  intro V hV
  let L : Submodule (𝓞 E) (Fin 1 → E) :=
    Submodule.pi Set.univ (fun _ => LinearMap.range (Algebra.linearMap (𝓞 E) E))
  have hL : Submodule.span E (L : Set (Fin 1 → E)) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have h1 : (fun _ => (1 : E)) ∈ L := fun i _ => ⟨1, map_one (algebraMap (𝓞 E) E)⟩
    have h3 := Submodule.smul_mem _ (v 0) (Submodule.subset_span (R := E) h1)
    convert h3 using 1
    funext i
    rw [Subsingleton.elim i 0]
    simp
  obtain ⟨hopen, hbas⟩ := GlobalTheory.T.isOpen_nsmul_adelicCompletionOfVectorSet F E 1 L hL
  have hV0 : {y : RA F E | 1 + y ∈ V} ∈ 𝓝 (0 : RA F E) := by
    have : Continuous (fun y : RA F E => 1 + y) := continuous_const_add 1
    have h := this.tendsto 0
    rw [add_zero] at h
    exact h hV
  obtain ⟨n, hn, hnV⟩ := hbas _ hV0
  have hhat : ∀ y ∈ hat F (L : Set (Fin 1 → E)), y 0 ∈ intHat F E := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, w, hw, rfl⟩ := hx
      obtain ⟨s, hs⟩ := hw 0 (Set.mem_univ _)
      have := tmul_mem F E a ha s
      change a ⊗ₜ[F] (w 0) ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))
      rw [← hs]
      exact this
    | zero => exact zero_mem _
    | add x y _ _ h1 h2 => exact add_mem h1 h2
    | neg x _ h => exact neg_mem h
  have hcont : Continuous (fun (u : RA F E) (_ : Fin 1) => u + (-1)) :=
    continuous_pi fun _ => continuous_id.add continuous_const
  have hN := ((hopen (2 * n) (by omega)).preimage hcont).mem_nhds (x := 1)
    ⟨0, zero_mem _, by funext i; simp⟩
  filter_upwards [hN] with u hu hn1
  obtain ⟨z, hz, hz2⟩ := hu
  have hz3 : u - 1 = (2 * n) • z 0 := by
    rw [sub_eq_add_neg]
    exact congrFun hz2 0
  obtain ⟨x, y, hxy, hx, ⟨p, hp, rfl⟩, ⟨q, hq, rfl⟩⟩ := finite_root F E c h2 hc hP n u (z 0) (hhat z hz) hz3 hn1
  exact ⟨_, hnV p hp, _, hnV q hq, hxy, hx⟩
end GlobalTheory.AdLat.RootNear
