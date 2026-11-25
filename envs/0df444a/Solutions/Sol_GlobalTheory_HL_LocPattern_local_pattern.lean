-- Prove2me | solution 1 for GlobalTheory.HL.LocPattern.local_pattern
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:32:25.454644+00:00
-- url     : https://prove2.me/submissions/6bf967e4-e79c-4c95-b1a6-014bee9da829

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalCommonStabiliserBlockUnitriangularOnFrame
import Theorems.Thm_GlobalTheory_HL_LocPattern_m_zero
import Theorems.Thm_GlobalTheory_HL_LocPattern_ab_one
import Theorems.Thm_GlobalTheory_HL_LocPattern_ba_one
import Theorems.Thm_GlobalTheory_HL_LocPattern_D_ne
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_HL_FrameOnto_unipotent_onto
import Theorems.Thm_GlobalTheory_HL_FrameStab_stab_eq
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LocPattern
open GlobalTheory.HL.Eichler
namespace GlobalTheory.HL.LocPattern
theorem _root_.solution : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ (p : HeightOneSpectrum (𝓞 F)) (h : (G.S p).GLV), h ∈ (G.S p).St → ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep, (∀ i j, ¬ (i < j ∧ ∀ l : Fin (r + 2), ((i : Fin (r + 1)) : ℕ) < l → (l : ℕ) ≤ ((j : Fin (r + 1)) : ℕ) → G.D l = 0) → s i j = if i = j then 1 else 0) ∧ (∀ j, h (A.bc p (G.f j)) = ∑ i, s i j • A.bc p (G.f i)) ∧ ((∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = G.c p) → h ∈ (G.S p).K0 → IsIntM (A.L p) s) := by
  intro F E _ _ _ _ _ sig A r k G p h hh
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  obtain ⟨hN1, hN2, -⟩ := GlobalTheory.HL.FrameOnto.unipotent_onto (A.L p) r k (G.S p)
  obtain ⟨m, hm, hmf⟩ := hN1 h hh.1
  obtain ⟨m', hm', hmf'⟩ := hN2 h hh.2
  have heq : cT (A.L p) m * (G.S p).Zh * m' = (G.S p).Zh :=
    ((GlobalTheory.HL.FrameStab.stab_eq (A.L p) r k (G.S p)).2 m m' hm hm').2 ⟨h, hh, hmf, hmf'⟩
  refine ⟨fun i j => algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (j : ℕ))) * m i j *
    algebraMap (A.loc p).Fp (A.loc p).Ep ((((G.c p)⁻¹ ^ (r - (i : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp),
    ?_, ?_, ?_⟩
  · intro i j hij
    beta_reduce
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · have hex : ∃ l : Fin (r + 2), (i : ℕ) < l ∧ (l : ℕ) ≤ j ∧ G.D l ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hij ⟨hlt, fun l h1 h2 => hc l h1 h2⟩
      obtain ⟨l, h1, h2, h3⟩ := hex
      rw [if_neg hlt.ne, m_zero (G.S p) m m' hm' heq l (D_ne G p l h3) i j h1 h2]
      simp
    · rw [if_pos rfl, hm.2, mul_one, ab_one]
    · rw [if_neg hgt.ne', hm.1 i j hgt]
      simp
  · intro j
    beta_reduce
    rw [← G.f_eq p j, map_smul, hmf j, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← G.f_eq p i, smul_smul, smul_smul, mul_assoc (_ * m i j), ba_one, mul_one]
  · rintro ⟨u, hu⟩ hK i j
    have hli : LinearIndependent (A.loc p).Ep (G.S p).f :=
      (GlobalTheory.FrameBasic.main (A.L p) r k (G.S p)).1.comp Sum.inl Sum.inl_injective
    have hmem : h ((G.S p).f j) ∈ Submodule.span (A.L p).O (Set.range (G.S p).f) := by
      have h1 : h • Submodule.span (A.L p).O (Set.range (G.S p).f) =
          Submodule.span (A.L p).O (Set.range (G.S p).f) := hK.1.2
      rw [← h1]
      exact Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.subset_span ⟨j, rfl⟩)
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hmem
    have hb' : ∑ i, ((b i : (A.L p).O) : (A.loc p).Ep) • (G.S p).f i = h ((G.S p).f j) := by
      rw [← hb]
      exact Finset.sum_congr rfl fun i _ => (Subring.smul_def _ _).symm
    have hmb : m i j = b i := by
      have := Fintype.linearIndependent_iff.1 hli (fun i => ((b i : (A.L p).O) : (A.loc p).Ep) - m i j) (by
        simp only [sub_smul, Finset.sum_sub_distrib, hb', hmf j, sub_self])
      exact (sub_eq_zero.1 (this i)).symm
    have hO : ∀ (y : 𝒪[(A.loc p).Fp]) (n : ℕ),
        algebraMap (A.loc p).Fp (A.loc p).Ep ((y : (A.loc p).Fp) ^ n) ∈ (A.L p).O := by
      intro y n
      rw [map_pow]
      refine pow_mem (((A.L p).O_def _).2 ?_) n
      rw [show (y : (A.loc p).Fp) = algebraMap 𝒪[(A.loc p).Fp] (A.loc p).Fp y from rfl,
        ← IsScalarTower.algebraMap_apply]
      exact isIntegral_algebraMap
    have hinv : (((G.c p)⁻¹ : ((A.loc p).Fp)ˣ) : (A.loc p).Fp) = (((u⁻¹ : (𝒪[(A.loc p).Fp])ˣ) : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) := by
      rw [Units.val_inv_eq_inv_val, ← hu]
      symm
      apply eq_inv_of_mul_eq_one_left
      exact congrArg (fun x : 𝒪[(A.loc p).Fp] => (x : (A.loc p).Fp)) (Units.inv_mul u)
    refine Subring.mul_mem _ (Subring.mul_mem _ ?_ (hmb ▸ (b i).2)) ?_
    · rw [← hu]; exact hO u _
    · rw [Units.val_pow_eq_pow_val, hinv]; exact hO _ _
end GlobalTheory.HL.LocPattern
