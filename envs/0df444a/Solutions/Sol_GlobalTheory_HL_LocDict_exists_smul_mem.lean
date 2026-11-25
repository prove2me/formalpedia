-- Prove2me | solution 1 for GlobalTheory.HL.LocDict.exists_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:40:30.20734+00:00
-- url     : https://prove2.me/submissions/c2856fa7-67cc-41f8-ad06-ecf9d52a7281

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLatIffMemLocP
import Theorems.Thm_GlobalTheory_HL_LocDict_exists_dual
import Theorems.Thm_GlobalTheory_HL_LocDict_lat_transfer
import Theorems.Thm_GlobalTheory_HL_LocDict_exists_den
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_PlacesInt_integers_local
import Theorems.Thm_GlobalTheory_HL_PlacesInt_nontrivial_Ep
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LocDict
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} (A : Places F E sig) {n : ℕ} (p : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.HL.LocDict
theorem _root_.solution (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Λ.FG) (x : Fin n → E)
    (hx : A.bc p x ∈ A.lat p Λ) :
    ∃ s : 𝓞 F, s ∉ p.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) s • x ∈ Λ := by
  obtain ⟨m, b, Φ, hb, hΦ, hy⟩ := exists_dual (K := E) Λ hΛ
  let Pr : (Fin n → E) →ₗ[E] (Fin n → E) := LinearMap.id - ∑ i, (Φ i).smulRight (b i)
  have hPr : ∀ y, Pr y = y - ∑ i, Φ i y • b i := fun y => by
    simp [Pr, LinearMap.sum_apply]
  have hx0 : Pr x = 0 := by
    have h1 := lat_transfer A p Λ Pr ⊥ (fun y hy' => by
      have : Pr y = 0 := by rw [hPr, ← hy y hy', sub_self]
      have h0 : A.bc p (0 : Fin n → E) = 0 := by
        funext i
        exact map_zero (A.loc p).ιE
      rw [this, h0]
      exact Submodule.zero_mem _) hx
    have h2 : A.bc p (Pr x) = 0 := h1
    haveI := PlacesInt.nontrivial_Ep (A.loc p)
    funext i
    exact (A.loc p).ιE.injective (by simpa [Places.bc] using congrFun h2 i)
  have hxs : x = ∑ i, Φ i x • b i := by
    rw [hPr, sub_eq_zero] at hx0
    exact hx0
  let N : Submodule (A.L p).O (Fin m → (A.loc p).Ep) :=
    Submodule.pi Set.univ fun _ => (LinearMap.range (Algebra.linearMap (A.L p).O (A.loc p).Ep))
  have hC := lat_transfer A p Λ (LinearMap.pi Φ) N (fun y hy' i _ => by
    obtain ⟨o, ho⟩ := hΦ i y hy'
    have hoO : (A.loc p).ιE (algebraMap (𝓞 E) E o) ∈ (A.L p).O :=
      (PlacesInt.integers_local A).1 _ |>.2 ⟨o, rfl⟩ p
    exact ⟨⟨_, hoO⟩, by simp [Places.bc, ho]; rfl⟩) hx
  have hC' : ∀ i, (A.loc p).ιE (Φ i x) ∈ (A.L p).O := fun i => by
    obtain ⟨o, ho⟩ := hC i (Set.mem_univ _)
    have : (A.loc p).ιE (Φ i x) = o := ho.symm
    rw [this]
    exact o.2
  choose s hs o ho using fun i => exists_den A p (Φ i x) (hC' i)
  refine ⟨∏ i, s i, fun h => ?_, ?_⟩
  · obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := p.isPrime)).1 h
    exact hs i hi
  · rw [hxs, Finset.smul_sum]
    refine Λ.sum_mem fun i _ => ?_
    have e : (algebraMap (𝓞 F) (𝓞 E) (∏ j, s j)) • (Φ i x • b i)
        = (algebraMap (𝓞 F) (𝓞 E) (∏ j ∈ Finset.univ.erase i, s j) * o i) • b i := by
      rw [← algebraMap_smul E (algebraMap (𝓞 F) (𝓞 E) (∏ j, s j)), smul_smul,
        ← algebraMap_smul E (_ * o i)]
      congr 1
      rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ i), map_mul, map_mul, map_mul,
        ← ho i, ← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E (s i)]
      ring
    rw [e]
    exact Λ.smul_mem _ (hb i)
end GlobalTheory.HL.LocDict
