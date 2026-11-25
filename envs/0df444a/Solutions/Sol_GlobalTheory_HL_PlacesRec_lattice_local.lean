-- Prove2me | solution 1 for GlobalTheory.HL.PlacesRec.lattice_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:20:33.929855+00:00
-- url     : https://prove2.me/submissions/b7a6a1a3-08b2-4c11-bc1f-14b49ca9519d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsSide
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NumberFieldLatticeDeterminedByLocalLattices
import Theorems.Thm_GlobalTheory_HL_PlacesRec_exists_common
import Theorems.Thm_GlobalTheory_HL_PlacesRec_bc_smul
import Theorems.Thm_GlobalTheory_HL_PlacesRec_bc_single
import Theorems.Thm_GlobalTheory_HL_PlacesRec_lat_span
import Theorems.Thm_GlobalTheory_HL_PlacesRec_mem_of_forall_lat
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_PlacesInt_integers_local
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PlacesRec
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {n : ℕ}
namespace GlobalTheory.HL.PlacesRec
theorem _root_.solution : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E Λ → (∀ x, x ∈ Λ ↔ ∀ p, A.bc p x ∈ A.lat p Λ) ∧ (∀ p, IsLat (A.L p) (A.lat p Λ)) ∧ {p | A.lat p Λ ≠ Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : Fin n → (A.loc p).Ep))}.Finite := by
  intro F E _ _ _ _ _ sig A n Λ h
  obtain ⟨D, hD, hm⟩ := exists_common Λ h.span_eq_top
  have hDE : (D : E) ≠ 0 := by simpa using hD
  have hsingle : ∀ p (i : Fin n), (Pi.single i 1 : Fin n → (A.loc p).Ep) =
      (A.loc p).ιE (D : E)⁻¹ • A.bc p (D • (Pi.single i 1 : Fin n → E)) := by
    intro p i
    rw [← bc_smul, ← bc_single A p i]
    congr 1
    ext j
    simp only [Pi.smul_apply, Algebra.smul_def (R := 𝓞 E) (A := E), smul_eq_mul]
    change _ = ((D : E))⁻¹ * ((D : E) * _)
    field_simp
  obtain ⟨S, hS⟩ := h.fg
  refine ⟨fun x => ⟨fun hx p => Submodule.subset_span ⟨x, hx, rfl⟩, mem_of_forall_lat A Λ h x⟩,
    fun p => ⟨?_, ?_⟩, ?_⟩
  · rw [← hS, lat_span]
    exact Submodule.fg_span (S.finite_toSet.image _)
  · rw [eq_top_iff]
    intro v _
    have hv : v = ∑ i, v i • (Pi.single i 1 : Fin n → (A.loc p).Ep) := by
      ext j
      simp [Pi.single_apply]
    rw [hv]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    rw [hsingle p i]
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      (Submodule.subset_span ⟨_, hm i, rfl⟩))
  · have hfin := (PlacesInt.integers_local A).2.1
    have h1 : (⋃ s ∈ (S : Set (Fin n → E)), ⋃ i, {p | (A.loc p).ιE (s i) ∉ (A.L p).O}).Finite :=
      S.finite_toSet.biUnion fun s _ => Set.finite_iUnion fun i => hfin (s i)
    refine (h1.union (hfin (D : E)⁻¹)).subset fun p hp => ?_
    by_contra hnot
    apply hp
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists, not_not] at hnot
    obtain ⟨hn1, hn2⟩ := hnot
    apply le_antisymm
    · rw [← hS, lat_span]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨s, hs, rfl⟩
      have hv : A.bc p s = ∑ i, (⟨_, hn1 s hs i⟩ : (A.L p).O) •
          (Pi.single i 1 : Fin n → (A.loc p).Ep) := by
        ext j
        simp [Pi.single_apply, Places.bc, Subring.smul_def]
      rw [SetLike.mem_coe, hv]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨i, rfl⟩)
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      have h2 := Submodule.smul_mem (A.lat p Λ) (⟨_, hn2⟩ : (A.L p).O)
        (Submodule.subset_span ⟨_, hm i, rfl⟩ : A.bc p (D • (Pi.single i 1 : Fin n → E)) ∈ A.lat p Λ)
      rw [SetLike.mem_coe]
      beta_reduce
      rw [hsingle p i]
      exact h2
end GlobalTheory.HL.PlacesRec
