-- Prove2me | solution 1 for GlobalTheory.exists_basis_kaehler_uniformiser
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:52:32.801862+00:00
-- url     : https://prove2.me/submissions/197477d6-6f3d-4f8f-82d4-193ef9a56092

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_P2M_GlobalTheory_formMap__Multi_014b852379ac
import Theorems.Thm_GlobalTheory_dlogWedge_empty
import Theorems.Thm_GlobalTheory_ordTop_vw_zero
import Theorems.Thm_GlobalTheory_fracKaehlerBasis_apply
import Theorems.Thm_GlobalTheory_topFormCoeff_topFormGen
import Theorems.Thm_GlobalTheory_one_tmul_D_ne_zero
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15


attribute [local simp] GlobalTheory.formMap_ιMulti
attribute [local simp] GlobalTheory.dlogWedge_empty
attribute [local simp] GlobalTheory.ordTop_vw_zero
attribute [local simp] GlobalTheory.fracKaehlerBasis_apply
attribute [local simp] GlobalTheory.topFormCoeff_topFormGen

set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable (K : Type*) {V : Type*} [Field K] [PerfectField K] [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] [Algebra K V] [Algebra.EssFiniteType K V]
  [Algebra.FormallySmooth K V]
namespace GlobalTheory
theorem _root_.solution {t : V} (ht : Irreducible t) :
    ∃ (m : ℕ) (z : Fin (m + 1) → V) (b : Basis (Fin (m + 1)) V Ω[V⁄K]),
      z 0 = t ∧ ∀ k, b k = D K V (z k) := by
  classical
  let κ := ResidueField V
  let f : V → κ ⊗[V] Ω[V⁄K] := TensorProduct.mk V κ Ω[V⁄K] 1 ∘ D K V
  have hspan : Submodule.span κ (Set.range f) = ⊤ := by
    have := (map_tensorProduct_mk_eq_top (N := Submodule.span V (Set.range (D K V)))).mpr
      (span_range_derivation K V)
    rw [← Submodule.span_image, ← Set.range_comp, eq_top_iff, ← SetLike.coe_subset_coe,
      Submodule.top_coe] at this
    rw [eq_top_iff]
    exact Set.Subset.trans this (Submodule.span_subset_span _ _ _)
  have h₁ : LinearIndepOn κ f {t} := LinearIndepOn.singleton (one_tmul_D_ne_zero K ht)
  obtain ⟨T, -, htT, hT, hli⟩ := exists_linearIndepOn_extension h₁ (Set.subset_univ _)
  have hT' : Submodule.span κ (f '' T) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le, ← Set.image_univ]
    exact hT
  have hfin : Finite T := hli.linearIndependent.finite
  have hne : Nonempty T := ⟨⟨t, htT rfl⟩⟩
  obtain ⟨m, hm⟩ : ∃ m, Nat.card T = m + 1 := Nat.exists_eq_succ_of_ne_zero Nat.card_pos.ne'
  let e₀ : Fin (m + 1) ≃ T := (Finite.equivFinOfCardEq hm).symm
  let e : Fin (m + 1) ≃ T := (Equiv.swap 0 (e₀.symm ⟨t, htT rfl⟩)).trans e₀
  have : Module.FinitePresentation V Ω[V⁄K] := Module.finitePresentation_of_finite V _
  obtain ⟨b, hb⟩ := Module.exists_basis_of_basis_baseChange (R := V)
    (fun k => D K V (e k : V)) (hli.linearIndependent.comp e e.injective)
    (by
      rw [← hT']
      congr 1
      ext y
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨e k, (e k).2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨e.symm ⟨x, hx⟩, by simp [f]⟩)
    (Module.Flat.rTensor_preserves_injective_linearMap (maximalIdeal V).subtype
      Subtype.val_injective)
  exact ⟨m, fun k => e k, b, by simp [e], hb⟩
end GlobalTheory
