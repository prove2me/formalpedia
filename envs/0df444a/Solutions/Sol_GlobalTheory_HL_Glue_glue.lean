-- Prove2me | solution 1 for GlobalTheory.HL.Glue.glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:37:01.106959+00:00
-- url     : https://prove2.me/submissions/ab8152f9-a3b5-473d-b72c-a65c25a51745

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtensionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NumberFieldLatticeDeterminedByLocalLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNatMulMemIntegersQuadraticCompletionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalLatticeBetweenScaledStandardLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNatBoundLocalLatticesStandardAeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfIntegralAllQuadraticCompletionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NatCastIsUnitQuadraticCompletionAlmostAllStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLatticeOfSqueezedBetweenNatMultiplesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalLatticeLeCompletionGluedLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanSingleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsUniqueGlobalLatticeOfLocalLattices
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_T_exists_nat_bound_localLattices_standard_ae
import Theorems.Thm_GlobalTheory_T_exists_nat_mul_mem_integers_quadraticCompletion
import Theorems.Thm_GlobalTheory_T_isIntegral_of_integral_all_quadraticCompletions
import Theorems.Thm_GlobalTheory_T_isLattice_of_squeezed_between_nat_multiples
import Theorems.Thm_GlobalTheory_T_localLattice_le_completion_glued_lattice
import Theorems.Thm_GlobalTheory_T_local_lattice_between_scaled_standard_lattices
import Theorems.Thm_GlobalTheory_T_natCast_isUnit_quadraticCompletion_almost_all
import Theorems.Thm_GlobalTheory_T_numberField_lattice_determined_by_local_lattices
import Theorems.Thm_GlobalTheory_T_strong_approximation_additive_quadratic_extension
import Theorems.Thm_P2M_GlobalTheory_HL_Glue__E_mem_8736254c8d80
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Glue
namespace GlobalTheory.HL.Glue
theorem _root_.solution : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (n : ℕ) (Λ : ∀ p, Submodule (A.L p).O (Fin n → (A.loc p).Ep)), (∀ p, IsLat (A.L p) (Λ p)) → {p | Λ p ≠ Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : Fin n → (A.loc p).Ep))}.Finite → ∃! Γ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E Γ ∧ ∀ p, A.lat p Γ = Λ p := by
  intro F E _ _ _ _ _ sig A n Λ hlat hfin
  refine existsUnique_of_exists_of_unique ?_ ?_
  · have happ1 := (GlobalTheory.T.strong_approximation_additive_quadratic_extension A (fun _ => 1)
      (Set.finite_empty.subset fun p hp => hp ⟨1, by simp⟩)).2.1
    have h3 : ∀ p (y : (A.loc p).Ep), ∃ m : ℕ, m ≠ 0 ∧ (m : (A.loc p).Ep) * y ∈ (A.L p).O :=
      GlobalTheory.T.exists_nat_mul_mem_integers_quadraticCompletion A (fun y hy => by
        obtain ⟨x, hx⟩ := happ1 y hy
        exact ⟨x, fun p => by simpa using hx p⟩)
    obtain ⟨N, hN, hb⟩ := GlobalTheory.T.exists_nat_bound_localLattices_standard_ae A n Λ hfin fun p => GlobalTheory.T.local_lattice_between_scaled_standard_lattices A p n (Λ p) (hlat p) (h3 p)
    let Γ : Submodule (𝓞 E) (Fin n → E) :=
      { carrier := {x | ∀ p, A.bc p x ∈ Λ p}
        add_mem' := by
          intro x y hx hy p
          have : A.bc p (x + y) = A.bc p x + A.bc p y := by funext i; simp [Places.bc]
          rw [this]; exact (Λ p).add_mem (hx p) (hy p)
        zero_mem' := by
          intro p
          have : A.bc p (0 : Fin n → E) = 0 := by funext i; simp [Places.bc]
          rw [this]; exact (Λ p).zero_mem
        smul_mem' := by
          intro a x hx p
          have ha : (A.loc p).ιE (a : E) ∈ (A.L p).O := ιE_mem A p _ a.isIntegral_coe
          have : A.bc p (a • x) = (⟨_, ha⟩ : (A.L p).O) • A.bc p x := by
            funext i; simp [Places.bc, Subring.smul_def, Algebra.smul_def]; rfl
          rw [this]; exact (Λ p).smul_mem _ (hx p) }
    have hΓ : ∀ x, x ∈ Γ ↔ ∀ p, A.bc p x ∈ Λ p := fun x => Iff.rfl
    have hL : Submodule.IsLattice E Γ := by
      refine GlobalTheory.T.isLattice_of_squeezed_between_nat_multiples n Γ N hN (fun x hx p => ?_) (fun x hx i => ?_)
      · have : A.bc p ((N : E) • x) = (N : (A.loc p).Ep) • A.bc p x := by
          funext i; simp [Places.bc]
        rw [this]
        exact (hb p).1 _ fun i => ιE_mem A p _ (hx i)
      · refine GlobalTheory.T.isIntegral_of_integral_all_quadraticCompletions A _ fun p => ?_
        have := (hb p).2 _ (hx p) i
        simpa [Places.bc] using this
    refine ⟨Γ, hL, fun p => le_antisymm ?_ ?_⟩
    · exact Submodule.span_le.2 (by rintro _ ⟨x, hx, rfl⟩; exact hx p)
    · haveI := (A.loc p).char0
      refine GlobalTheory.T.localLattice_le_completion_glued_lattice A n Λ Γ N hΓ (fun q => (hb q).1) ?_ p
      have hc : ∀ q, (N : (A.loc q).Fp) ≠ 0 := fun q => by
        haveI := (A.loc q).char0; exact_mod_cast hN
      have happN := (GlobalTheory.T.strong_approximation_additive_quadratic_extension A (fun q => Units.mk0 _ (hc q))
        (by simpa using GlobalTheory.T.natCast_isUnit_quadraticCompletion_almost_all A N hN)).2.1
      intro y hy
      obtain ⟨x, hx⟩ := happN y hy
      exact ⟨x, fun q => by simpa using hx q⟩
  · rintro Γ₁ Γ₂ ⟨h1, e1⟩ ⟨h2, e2⟩
    ext x
    rw [(GlobalTheory.T.numberField_lattice_determined_by_local_lattices A n Γ₁ h1).1 x, (GlobalTheory.T.numberField_lattice_determined_by_local_lattices A n Γ₂ h2).1 x]
    simp only [e1, e2]
end GlobalTheory.HL.Glue
