-- Prove2me | solution 1 for GlobalTheory.HL.FrameClose.loc_close
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:36:57.159974+00:00
-- url     : https://prove2.me/submissions/b0968895-cca9-4023-a562-60a782b0627c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitriangularCloseToOneInverseCloseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PairingConjInverseAdjointCloseToOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemMaximalCompactOfIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalPairingMatrixInvMulSelfStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GlobalFramesJointGramInvMulSelfStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsCommonDenominatorForHermitianLatticeDataStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CloseOnCompletedLatticeOfCloseOnFramesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntCastIsUnitCompletionAlmostAllPlacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameMatrixCloseGivesLatticeCloseIntegral
import Theorems.Thm_GlobalTheory_HL_FrameClose_algebraMap_mem
import Theorems.Thm_GlobalTheory_HL_FrameClose_coord_scale
import Theorems.Thm_GlobalTheory_HL_FrameClose_pair_fix
import Theorems.Thm_GlobalTheory_HL_FrameClose_scale_int
import Theorems.Thm_GlobalTheory_HL_FrameClose_int_inv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_HL_FrameOnto_unipotent_onto
import Theorems.Thm_GlobalTheory_HL_GamInv_main
import Theorems.Thm_GlobalTheory_Sloc_CloseConj_main
import Theorems.Thm_GlobalTheory_T_mem_maximal_compact_of_integral
import Theorems.Thm_GlobalTheory_T_pairing_conj_inverseAdjoint_close_to_one
import Theorems.Thm_GlobalTheory_T_unitriangular_close_to_one_inverse_close
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameClose
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [IsNonarchimedeanLocalField F] [CharZero F]
namespace GlobalTheory.HL.FrameClose
theorem _root_.solution (L : LocE F E) (r k : ℕ) (S : Frames L r k) (c a t e : F)
    (Zi : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (h : S.GLV) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hc : c ≠ 0) (ha : a ∈ 𝒪[F]) (hac : a * c ∈ 𝒪[F]) (ht : t ∈ 𝒪[F]) (he : e ∈ 𝒪[F]) (he0 : e ≠ 0)
    (hZi : Zi * Matrix.of (fun i j : Fin (r + 1) => hf L S.Hm (algebraMap F E (c ^ (r - (j : ℕ))) • S.f' j)
      (algebraMap F E (c ^ (r - (i : ℕ))) • S.f i)) = 1)
    (hZ : ∀ i j : Fin (r + 1), algebraMap F E e * hf L S.Hm (algebraMap F E (c ^ (r - (j : ℕ))) • S.f' j)
      (algebraMap F E (c ^ (r - (i : ℕ))) • S.f i) ∈ L.O)
    (hZi' : ∀ i j, algebraMap F E e * Zi i j ∈ L.O) (hh : h ∈ S.St)
    (hM : ∀ j : Fin (r + 1), h (algebraMap F E (c ^ (r - (j : ℕ))) • S.f j) =
      ∑ i, M i j • (algebraMap F E (c ^ (r - (i : ℕ))) • S.f i))
    (hcl : ∀ i j, ∃ o ∈ L.O, (M - 1) i j = algebraMap F E (t * e ^ 2 * a ^ r) * o) :
    h ∈ S.K0 ∧ ∃ M' : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      (∀ j : Fin (r + 1), h (algebraMap F E (c ^ (r - (j : ℕ))) • S.f' j) =
        ∑ i, M' i j • (algebraMap F E (c ^ (r - (i : ℕ))) • S.f' i)) ∧
      ∀ i j, ∃ o ∈ L.O, (M' - 1) i j = algebraMap F E (t * a ^ r) * o := by
  have := L.free
  have hnt : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)
  have hinj : Function.Injective (algebraMap F E) := (algebraMap F E).injective
  obtain ⟨hli, -⟩ := GlobalTheory.FrameBasic.main L r k S
  have hli1 : LinearIndependent E S.f := (linearIndependent_sum.1 hli).1
  obtain ⟨hN, hN', -⟩ := GlobalTheory.HL.FrameOnto.unipotent_onto L r k S
  have hhN : h ∈ S.N := (Subgroup.mem_inf.1 hh).1
  have hhN' : h ∈ S.N' := (Subgroup.mem_inf.1 hh).2
  obtain ⟨s, hs, hsf⟩ := hN h hhN
  obtain ⟨s', hs', hsf'⟩ := hN' h hhN'
  have hiso : ∀ x y, hf L S.Hm (h x) (h y) = hf L S.Hm x y := hhN.1.1
  set cp : Fin (r + 1) → E := fun j => algebraMap F E (c ^ (r - (j : ℕ))) with hcp
  have hcpu : ∀ j, IsUnit (cp j) := fun j => (IsUnit.mk0 _ (pow_ne_zero _ hc)).map (algebraMap F E)

  have hMs := coord_scale S.f hli1 h cp s M hsf hM
  have hMlow : ∀ i j, j < i → M i j = 0 := by
    intro i j hij
    have := hMs i j
    rw [hs.1 i j hij, mul_zero] at this
    exact (hcpu i).mul_left_eq_zero.1 this
  have hMdiag : ∀ i, M i i = 1 := by
    intro i
    have := hMs i i
    rw [hs.2 i, mul_one] at this
    exact (hcpu i).mul_left_inj.1 (this.trans (one_mul _).symm)

  set M' : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
    Matrix.of fun i j => algebraMap F E (c ^ (r - (j : ℕ)) / c ^ (r - (i : ℕ))) * s' i j with hM'def
  have hM' : ∀ j, h (cp j • S.f' j) = ∑ i, M' i j • (cp i • S.f' i) := by
    intro j
    rw [map_smul, hsf' j, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, smul_smul]
    congr 1
    have e1 : algebraMap F E (c ^ (r - (j : ℕ)) / c ^ (r - (i : ℕ))) * algebraMap F E (c ^ (r - (i : ℕ))) =
        algebraMap F E (c ^ (r - (j : ℕ))) := by
      rw [← map_mul, div_mul_cancel₀ _ (pow_ne_zero _ hc)]
    simp only [hM'def, hcp, Matrix.of_apply]
    linear_combination (-(s' i j)) * e1

  have hpair := pair_fix L S.Hm (fun j => cp j • S.f j) (fun j => cp j • S.f' j) h hiso M M' hM hM'
  have htO : algebraMap F E (t * e ^ 2 * a ^ r) ∈ L.O :=
    algebraMap_mem L (mul_mem (mul_mem ht (pow_mem he _)) (pow_mem ha _))
  obtain ⟨Mi, hMi1, hMi2, hMi⟩ := GlobalTheory.T.unitriangular_close_to_one_inverse_close L (r + 1) M _ htO hMlow hMdiag hcl
  have hcl' := GlobalTheory.T.pairing_conj_inverseAdjoint_close_to_one L (r + 1) _ Zi M Mi M' _ (algebraMap F E e) htO
    (by rw [L.cj_fix]; exact ⟨_, rfl⟩) hZi hZ hZi' hMi1 hMi2 hMi hpair
  have heu : IsUnit (algebraMap F E e) := (IsUnit.mk0 _ he0).map (algebraMap F E)
  have hM'cl : ∀ i j, ∃ o ∈ L.O, (M' - 1) i j = algebraMap F E (t * a ^ r) * o := by
    intro i j
    obtain ⟨o, ho, hoe⟩ := hcl' i j
    refine ⟨o, ho, ?_⟩
    have : algebraMap F E e * algebraMap F E e * ((M' - 1) i j - algebraMap F E (t * a ^ r) * o) = 0 := by
      rw [mul_sub, hoe]
      simp only [map_mul, map_pow]
      ring
    exact sub_eq_zero.1 ((heu.mul heu).mul_right_eq_zero.1 this)
  refine ⟨?_, M', hM', hM'cl⟩
  have hsO : ∀ i j, s i j ∈ L.O := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · refine scale_int L c a (t * e ^ 2) hc ha hac (mul_mem ht (pow_mem he _)) i j hij (M i j) (s i j) ?_ (hMs i j)
      obtain ⟨o, ho, hoe⟩ := hcl i j
      refine ⟨o, ho, ?_⟩
      rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt hij), sub_zero] at hoe
      rw [hoe]
    · rw [hs.2 i]; exact L.O.one_mem
    · rw [hs.1 i j hij]; exact L.O.zero_mem
  have hs'O : ∀ i j, s' i j ∈ L.O := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · refine scale_int L c a t hc ha hac ht i j hij (M' i j) (s' i j) ?_ ?_
      · obtain ⟨o, ho, hoe⟩ := hM'cl i j
        refine ⟨o, ho, ?_⟩
        rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt hij), sub_zero] at hoe
        rw [hoe]
      · simp only [hM'def, Matrix.of_apply]
        rw [mul_comm _ (s' i j), mul_assoc, ← map_mul, div_mul_cancel₀ _ (pow_ne_zero _ hc), mul_comm]
    · rw [hs'.2 i]; exact L.O.one_mem
    · rw [hs'.1 i j hij]; exact L.O.zero_mem
  obtain ⟨si, hsi, hsiO⟩ := int_inv L s hs.1 hs.2 hsO
  obtain ⟨si', hsi', hsi'O⟩ := int_inv L s' hs'.1 hs'.2 hs'O
  exact GlobalTheory.T.mem_maximal_compact_of_integral L r k S h s si s' si' hh hsO hsiO hsi hs'O hsi'O hsi' hsf hsf'
end GlobalTheory.HL.FrameClose
