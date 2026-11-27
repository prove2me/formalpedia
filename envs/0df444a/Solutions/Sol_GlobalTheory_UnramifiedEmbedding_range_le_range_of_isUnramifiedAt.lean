-- Prove2me | solution 1 for GlobalTheory.UnramifiedEmbedding.range_le_range_of_isUnramifiedAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:39:44.937829+00:00
-- url     : https://prove2.me/submissions/0484c829-1213-4efc-aa9f-79d5d8b62be0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GaloisOfPrimePowerDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RangeLeRangeOfIsUnramifiedAt
import Theorems.Thm_GlobalTheory_UnramifiedEmbedding_algHom_eq_of_residue_eq
import Theorems.Thm_GlobalTheory_UnramifiedEmbedding_quotientMap_bijective
import Theorems.Thm_GlobalTheory_exists_algHom_lift_of_smooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IsLocalRing NumberField
open GlobalTheory GlobalTheory.UnramifiedEmbedding
namespace GlobalTheory.UnramifiedEmbedding
theorem _root_.solution
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [IsAlgClosed (ResidueField O)]
    (l : ℕ) [Fact l.Prime] (hl : (l : O) ∈ maximalIdeal O)
    (e : FractionRing O →+* ℂ)
    (K₀ L : Type) [Field K₀] [NumberField K₀] [Field L] [NumberField L] [Algebra K₀ L]
    (ι : K₀ →+* FractionRing O) (σ : L →+* ℂ) (hσ : σ.comp (algebraMap K₀ L) = e.comp ι)
    (hur : ∀ (P : Ideal (𝓞 L)) [P.IsPrime], (l : 𝓞 L) ∈ P → Algebra.IsUnramifiedAt (𝓞 K₀) P) :
    σ.range ≤ e.range := by
  classical
  have hint : ∀ x : 𝓞 K₀, ∃ o : O, algebraMap O (FractionRing O) o = ι x := fun x =>
    IsIntegrallyClosed.isIntegral_iff.1
      (x.isIntegral_coe.map_of_comp_eq (Int.castRingHom O) ι (RingHom.ext_int _ _))
  choose g₀ hg₀ using hint
  have hinj := IsFractionRing.injective O (FractionRing O)
  let ιO : 𝓞 K₀ →+* O :=
    { toFun := g₀
      map_one' := hinj (by simp [hg₀])
      map_mul' := fun x y => hinj (by simp [hg₀])
      map_zero' := hinj (by simp [hg₀])
      map_add' := fun x y => hinj (by simp [hg₀]) }
  have hιO : ∀ x, algebraMap O (FractionRing O) (ιO x) = ι x := hg₀
  letI : Algebra (𝓞 K₀) O := ιO.toAlgebra
  letI : Algebra O ℂ := (e.comp (algebraMap O (FractionRing O))).toAlgebra
  have hOC : ∀ o : O, algebraMap O ℂ o = e (algebraMap O (FractionRing O) o) := fun _ => rfl
  let S := integralClosure O ℂ
  have hOS : Function.Injective (algebraMap O S) := fun a b h => by
    have := congrArg (fun s : S => (s : ℂ)) h
    simp only [Subalgebra.coe_algebraMap, hOC] at this
    exact hinj (e.injective this)
  obtain ⟨M, hMmax, hMc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := S) (maximalIdeal O)
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hOS]; exact bot_le)
  let σA : 𝓞 L →+* S := (σ.comp (algebraMap (𝓞 L) L)).codRestrict S fun a =>
    (a.isIntegral_coe.map_of_comp_eq (Int.castRingHom O) σ (RingHom.ext_int _ _) :)
  have hσA : ∀ a, (σA a : ℂ) = σ a := fun _ => rfl
  have hSR : ∀ r : 𝓞 K₀, σA (algebraMap (𝓞 K₀) (𝓞 L) r) = algebraMap O S (ιO r) := fun r => by
    apply Subtype.ext
    rw [hσA, Subalgebra.coe_algebraMap, hOC, hιO]
    exact congrArg (fun φ => φ (r : K₀)) hσ
  let P := M.comap σA
  have hlP : (l : 𝓞 L) ∈ P := by
    show σA l ∈ M
    rw [map_natCast, ← map_natCast (algebraMap O S), ← Ideal.mem_comap, hMc]
    exact hl
  haveI := hur P hlP
  haveI : Algebra.FinitePresentation (𝓞 K₀) (𝓞 L) :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  haveI : Module.Flat (𝓞 K₀) (𝓞 L) := IsDedekindDomain.flat_iff_torsion_eq_bot.2 (by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨r, hr⟩, hrx⟩ := hx
    have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
    have : algebraMap (𝓞 K₀) (𝓞 L) r * x = 0 := by rw [← Algebra.smul_def]; exact hrx
    rcases mul_eq_zero.1 this with h | h
    · exact absurd ((FaithfulSMul.algebraMap_injective _ _) (h.trans (map_zero _).symm)) hr0
    · exact h)
  obtain ⟨f, hfP, hfU⟩ := Algebra.exists_formallyUnramified_of_isUnramifiedAt (R := 𝓞 K₀) P
  haveI : Algebra.FinitePresentation (𝓞 K₀) (Localization.Away f) :=
    .trans _ (𝓞 L) _
  haveI : Module.Flat (𝓞 K₀) (Localization.Away f) := .trans _ (𝓞 L) _
  haveI : Algebra.Etale (𝓞 K₀) (Localization.Away f) := Algebra.Etale.of_formallyUnramified_of_flat
  haveI : Algebra.IsEtaleAt (𝓞 K₀) P :=
    Algebra.basicOpen_subset_etaleLocus_iff_etale.2 this
      (show (⟨P, inferInstance⟩ : PrimeSpectrum (𝓞 L)) ∈ PrimeSpectrum.basicOpen f from hfP)
  obtain ⟨g, hgP, hgE⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := 𝓞 K₀) P
  letI : Field (O ⧸ maximalIdeal O) := Ideal.Quotient.field _
  let q := Ideal.quotientMap M (algebraMap O S) hMc.ge
  have hq := quotientMap_bijective M hMc
  let qe := RingEquiv.ofBijective q hq
  let φ₀ : 𝓞 L →+* O ⧸ maximalIdeal O := qe.symm.toRingHom.comp ((Ideal.Quotient.mk M).comp σA)
  have hφ₀ : ∀ a, q (φ₀ a) = Ideal.Quotient.mk M (σA a) := fun a => qe.apply_symm_apply _
  have hφg : IsUnit (φ₀ g) := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hgP
    show σA g ∈ M
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hφ₀, h0, map_zero]
  let φr : Localization.Away g →+* O ⧸ maximalIdeal O := IsLocalization.Away.lift g hφg
  have hφr : ∀ a, φr (algebraMap _ _ a) = φ₀ a := fun a => IsLocalization.lift_eq _ _
  let φ : Localization.Away g →ₐ[𝓞 K₀] O ⧸ maximalIdeal O :=
    { φr with
      commutes' := fun r => by
        change φr (algebraMap (𝓞 K₀) (Localization.Away g) r) = _
        rw [IsScalarTower.algebraMap_apply (𝓞 K₀) (𝓞 L) (Localization.Away g), hφr]
        apply hq.1
        rw [hφ₀, hSR]
        rfl }
  haveI := hgE
  obtain ⟨ψ, hψ⟩ := GlobalTheory.exists_algHom_lift_of_smooth (maximalIdeal O)
    (Ideal.Quotient.mkₐ (𝓞 K₀) (maximalIdeal O)) Ideal.Quotient.mk_surjective
    (fun b => Ideal.Quotient.eq_zero_iff_mem.symm) φ
  haveI := hMmax
  let T := Localization.AtPrime M
  letI : Algebra (𝓞 K₀) T := ((algebraMap S T).comp ((algebraMap O S).comp ιO)).toAlgebra
  have hgT : IsUnit ((algebraMap S T).comp σA g) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff T M (σA g)).2 hgP
  let χ₂r : Localization.Away g →+* T := IsLocalization.Away.lift g hgT
  have hχ₂r : ∀ a, χ₂r (algebraMap _ _ a) = algebraMap S T (σA a) := fun a =>
    IsLocalization.lift_eq _ _
  let χ₁ : Localization.Away g →ₐ[𝓞 K₀] T :=
    { (algebraMap S T).comp ((algebraMap O S).comp ψ.toRingHom) with
      commutes' := fun r => by
        change algebraMap S T (algebraMap O S (ψ (algebraMap _ _ r))) = _
        rw [ψ.commutes]; rfl }
  let χ₂ : Localization.Away g →ₐ[𝓞 K₀] T :=
    { χ₂r with
      commutes' := fun r => by
        change χ₂r (algebraMap (𝓞 K₀) (Localization.Away g) r) = _
        rw [IsScalarTower.algebraMap_apply (𝓞 K₀) (𝓞 L) (Localization.Away g), hχ₂r, hSR]
        rfl }
  have hres : ∀ a : 𝓞 L,
      algebraMap O S (ψ (algebraMap _ (Localization.Away g) a)) - σA a ∈ M := by
    intro a
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
    have h1 := congrArg (fun φ' : Localization.Away g →ₐ[𝓞 K₀] _ => φ' (algebraMap _ _ a)) hψ
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h1
    change q (Ideal.Quotient.mk _ (ψ _)) = _
    rw [h1]
    change q (φr _) = _
    rw [hφr, hφ₀]
  have hχ : χ₁ = χ₂ := algHom_eq_of_residue_eq (fun s => by
    have : (residue T).comp χ₁.toRingHom = (residue T).comp χ₂.toRingHom := by
      refine IsLocalization.ringHom_ext (Submonoid.powers g) (RingHom.ext fun a => ?_)
      simp only [RingHom.comp_apply]
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
      change algebraMap S T _ - χ₂r (algebraMap _ _ a) ∈ _
      rw [hχ₂r, ← map_sub]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff T M _).2 (hres a)
    exact congrArg (fun j => j s) this)
  have hA : ∀ a : 𝓞 L,
      σ a = e (algebraMap O (FractionRing O) (ψ (algebraMap _ (Localization.Away g) a))) := by
    intro a
    have h := congrArg (fun χ : Localization.Away g →ₐ[𝓞 K₀] T => χ (algebraMap _ _ a)) hχ
    change algebraMap S T _ = χ₂r _ at h
    rw [hχ₂r] at h
    have h' := IsLocalization.injective T M.primeCompl_le_nonZeroDivisors h
    have h'' := congrArg (fun s : S => (s : ℂ)) h'
    simp only [Subalgebra.coe_algebraMap, hOC, hσA] at h''
    exact h''.symm
  rintro _ ⟨y, rfl⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) y
  refine ⟨algebraMap O _ (ψ (algebraMap _ (Localization.Away g) a)) /
    algebraMap O _ (ψ (algebraMap _ (Localization.Away g) b)), ?_⟩
  rw [map_div₀, map_div₀, ← hA, ← hA]
end GlobalTheory.UnramifiedEmbedding
