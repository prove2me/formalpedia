-- Prove2me | solution 1 for Module.finrank_iInf_ker_baseChange_eq_finrank_iInf_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/84b3783c-508e-59a9-bf7e-db42ff5b35f6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_finrank_iInf_ker_baseChange_eq_finrank_iInf_ker

open scoped TensorProduct

namespace G2Aux

open Submodule

theorem exists_finset_iInf_eq {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [IsArtinian R M]
    {ι : Type*} (S : ι → Submodule R M) : ∃ s : Finset ι, ⨅ i, S i = ⨅ i ∈ s, S i := by
  classical
  obtain ⟨m, ⟨s₀, rfl⟩, hmin⟩ := IsArtinian.set_has_minimal (R := R) (M := M)
    (Set.range fun s : Finset ι => ⨅ i ∈ s, S i) ⟨_, ∅, rfl⟩
  refine ⟨s₀, le_antisymm (le_iInf₂ fun i _ => iInf_le S i) (le_iInf fun j => ?_)⟩
  have hle : (⨅ i ∈ insert j s₀, S i) ≤ ⨅ i ∈ s₀, S i :=
    biInf_mono fun i hi => Finset.mem_insert_of_mem hi
  have hnlt : ¬ (⨅ i ∈ insert j s₀, S i) < ⨅ i ∈ s₀, S i := hmin _ ⟨insert j s₀, rfl⟩
  have heq : (⨅ i ∈ insert j s₀, S i) = ⨅ i ∈ s₀, S i := (eq_or_lt_of_le hle).resolve_right hnlt
  rw [← heq]
  exact biInf_le _ (Finset.mem_insert_self j s₀)

theorem baseChange_le_ker {F : Type*} [CommRing F] (K : Type*) [CommRing K] [Algebra F K]
    {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (f : V →ₗ[F] W) : (LinearMap.ker f).baseChange K ≤ LinearMap.ker (f.baseChange K) := by
  rw [Submodule.baseChange_eq_span, Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker] at hw ⊢
  rw [TensorProduct.mk_apply, LinearMap.baseChange_tmul, LinearMap.mem_ker.mp hw, TensorProduct.tmul_zero]

end G2Aux

open G2Aux in
theorem solution
    (F : Type) [Field F] (K : Type) [Field K] [Algebra F K]
    (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V]
    {ι : Type} (T : ι → (V →ₗ[F] V)) :
    Module.finrank K ↥(⨅ i, LinearMap.ker ((T i).baseChange K)) =
      Module.finrank F ↥(⨅ i, LinearMap.ker (T i)) := by
  classical
  set W : Submodule F V := ⨅ i, LinearMap.ker (T i) with hW

  have key : (⨅ i, LinearMap.ker ((T i).baseChange K)) = W.baseChange K := by
    apply le_antisymm
    ·
      haveI : IsArtinian F V := inferInstance
      obtain ⟨s, hs⟩ := exists_finset_iInf_eq (fun i => LinearMap.ker (T i))

      let Φ : V →ₗ[F] (↥s → V) := LinearMap.pi fun i : ↥s => T (i : ι)
      have hkerΦ : LinearMap.ker Φ = W := by
        rw [hW, hs, LinearMap.ker_pi]
        ext v
        simp only [Submodule.mem_iInf]
        exact ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i i.2⟩

      let Φbar : (V ⧸ W) →ₗ[F] (↥s → V) := W.liftQ Φ hkerΦ.ge
      have hΦbar : LinearMap.ker Φbar = ⊥ := Submodule.ker_liftQ_eq_bot _ _ _ hkerΦ.le
      obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_leftInverse_of_injective Φbar hΦbar
      have hinjK : Function.Injective (Φbar.baseChange K) := by
        intro a b hab
        have := congrArg (Ψ.baseChange K) hab
        rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hΨ,
          LinearMap.baseChange_id, LinearMap.id_apply, LinearMap.id_apply] at this

      have hex : Function.Exact (W.subtype.baseChange K) (W.mkQ.baseChange K) := by
        have h := lTensor_exact K (LinearMap.exact_subtype_mkQ W) (Submodule.mkQ_surjective W)
        intro x
        have hx := h x
        simp only [← LinearMap.baseChange_eq_ltensor] at hx
        rw [hx]
      intro x hx

      have h0 : (W.mkQ.baseChange K) x = 0 := by
        apply hinjK
        rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, Submodule.liftQ_mkQ]

        apply (TensorProduct.piRight F K K (fun _ : ↥s => V)).injective
        rw [map_zero]
        funext i
        have hcomp : ∀ y : K ⊗[F] V, TensorProduct.piRight F K K (fun _ : ↥s => V) (Φ.baseChange K y) i
            = (T (i : ι)).baseChange K y := by
          intro y
          induction y using TensorProduct.induction_on with
          | zero => simp
          | tmul k v => simp [Φ]
          | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]
        rw [hcomp, Pi.zero_apply]
        exact (Submodule.mem_iInf _).mp hx (i : ι)
      obtain ⟨y, hy⟩ := (hex x).mp h0
      exact ⟨y, hy⟩
    · rw [hW]
      refine le_iInf fun i => (Submodule.baseChange_mono _ (iInf_le _ i)).trans ?_
      exact baseChange_le_ker K (T i)
  rw [key]

  rw [← (Submodule.toBaseChange.toLinearEquiv K W).finrank_eq, Module.finrank_baseChange]

end S_Module_finrank_iInf_ker_baseChange_eq_finrank_iInf_ker
end P2MW
export P2MW.S_Module_finrank_iInf_ker_baseChange_eq_finrank_iInf_ker (solution)
