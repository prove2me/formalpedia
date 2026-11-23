-- Prove2me | solution 1 for GlobalTheory.SmGL.IwahoriOnto.exists_fixed_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:38.026605+00:00
-- url     : https://prove2.me/submissions/2a53d2bc-a643-4f46-bc04-6e77cb20318e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel Matrix Topology Filter
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.IwahoriOnto
variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.SmGL.IwahoriOnto
theorem _root_.solution {π : Representation ℂ G V} (hπ : IsSmooth π) {H : Subgroup G}
    (hH : IsCompact (H : Set G)) (f : V →ₗ[ℂ] W) (u : V) (hu : ∀ h ∈ H, f (π h u) = f u) :
    ∃ v ∈ fixed π H, f v = f u := by
  classical
  have hlc : IsLocallyConstant fun g : G => π g u := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
    have ho : IsOpen ((fun x => g⁻¹ * x) ⁻¹' {x : G | π x u = u}) := (hπ u).preimage (by fun_prop)
    filter_upwards [ho.mem_nhds (by simp)] with x hx
    have hx' : π (g⁻¹ * x) u = u := hx
    conv_rhs => rw [← hx']
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hH
  have hfin : (Set.range fun h : H => π h u).Finite :=
    (hlc.comp_continuous continuous_subtype_val).range_finite
  set S := hfin.toFinset with hS
  have hmem : ∀ w, w ∈ S ↔ ∃ h : H, π h u = w := fun w => by simp [hS]
  have hne : (S.card : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨u, (hmem u).2 ⟨1, by simp⟩⟩)
  have hst : ∀ (h : H) w, w ∈ S → π h w ∈ S := by
    intro h w hw
    obtain ⟨h', rfl⟩ := (hmem w).1 hw
    exact (hmem _).2 ⟨h * h', by simp⟩
  have hc : ∀ (g : G) w, π g⁻¹ (π g w) = w := fun g w => by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  refine ⟨(S.card : ℂ)⁻¹ • ∑ w ∈ S, w, fun h => ?_, ?_⟩
  · simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_smul, map_sum]
    congr 1
    refine Finset.sum_nbij' (π h) (π (h⁻¹ : H)) (hst h) (hst h⁻¹) (fun w _ => hc _ w)
      (fun w _ => ?_) fun _ _ => rfl
    simpa using hc (h : G)⁻¹ w
  · rw [map_smul, map_sum, Finset.sum_congr rfl (g := fun _ => f u), Finset.sum_const,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hne, one_smul]
    intro w hw
    obtain ⟨h, rfl⟩ := (hmem w).1 hw
    exact hu h h.2
end GlobalTheory.SmGL.IwahoriOnto
