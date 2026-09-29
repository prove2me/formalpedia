-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.ramificationIdx_eq_one_and_inertiaDeg_dvd_of_baseChange_of_unramified
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/5be1e268-1af3-572f-a4d6-a41a4508735d

import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_ramificationIdx_eq_one_and_inertiaDeg_dvd_of_baseChange_of_unramified

set_option autoImplicit false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Polynomial

namespace CMPAux

attribute [local instance] Ideal.Quotient.field

theorem isGalois_of_adjoin_range (K L K' M : Type) [Field K] [Field L] [Field K'] [Field M]
    [Algebra K L] [Algebra K K'] [Algebra K M] [Algebra L M] [Algebra K' M]
    [IsScalarTower K L M] [IsScalarTower K K' M] [FiniteDimensional K L] [IsGalois K L]
    (hcomp : ∀ x : M, x ∈ Algebra.adjoin K' (Set.range (algebraMap L M))) :
    IsGalois K' M := by
  obtain ⟨T, hT₁, hT₂⟩ := IsGalois.is_separable_splitting_field K L
  haveI := hT₂
  have hsplit : (T.map (algebraMap K L)).Splits := Polynomial.IsSplittingField.splits L T
  have hadj : Algebra.adjoin K (T.rootSet L) = ⊤ := Polynomial.IsSplittingField.adjoin_rootSet L T
  have hsplitM : ((T.map (algebraMap K K')).map (algebraMap K' M)).Splits := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    exact Polynomial.Splits.of_algHom hsplit (IsScalarTower.toAlgHom K L M)
  have h' : (T.map (algebraMap K K')).rootSet M = T.rootSet M := by
    ext a
    rw [Polynomial.mem_rootSet', Polynomial.mem_rootSet', Polynomial.map_map,
      ← IsScalarTower.algebraMap_eq, Polynomial.aeval_map_algebraMap]
  have hrange : Algebra.adjoin K (T.rootSet M) = (IsScalarTower.toAlgHom K L M).range :=
    (hsplit.adjoin_rootSet_eq_range (IsScalarTower.toAlgHom K L M)).mpr hadj
  have hsub : Set.range (algebraMap L M) ⊆ (Algebra.adjoin K' (T.rootSet M) : Set M) := by
    rintro _ ⟨y, rfl⟩
    have hy : algebraMap L M y ∈ Algebra.adjoin K (T.rootSet M) := by
      rw [hrange]; exact ⟨y, rfl⟩
    have hKK' : Algebra.adjoin K (T.rootSet M) ≤
        (Algebra.adjoin K' (T.rootSet M)).restrictScalars K :=
      Algebra.adjoin_le Algebra.subset_adjoin
    exact hKK' hy
  have hadjM : Algebra.adjoin K' ((T.map (algebraMap K K')).rootSet M) = ⊤ := by
    rw [h', eq_top_iff]
    intro x _
    exact Algebra.adjoin_le hsub (hcomp x)
  haveI : (T.map (algebraMap K K')).IsSplittingField K' M := ⟨hsplitM, hadjM⟩
  exact IsGalois.of_separable_splitting_field (p := T.map (algebraMap K K')) hT₁.map

theorem isSeparable_residueField (F M : Type) [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra F M] (p : Ideal (𝓞 F)) (P : Ideal (𝓞 M)) [p.IsMaximal] [P.IsMaximal]
    [P.LiesOver p] : Algebra.IsSeparable (𝓞 F ⧸ p) (𝓞 M ⧸ P) :=
  Algebra.IsAlgebraic.isSeparable_of_perfectField

theorem coe_smul_ringOfIntegers {F M : Type} [Field F] [Field M] [Algebra F M]
    (σ : M ≃ₐ[F] M) (x : 𝓞 M) : ((σ • x : 𝓞 M) : M) = σ (x : M) := rfl

theorem coe_algebraMap_ringOfIntegers {L M : Type} [Field L] [Field M] [Algebra L M]
    (y : 𝓞 L) : ((algebraMap (𝓞 L) (𝓞 M) y : 𝓞 M) : M) = algebraMap L M (y : L) := rfl

theorem eq_one_of_mem_inertia
    (K L K' M : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field K'] [NumberField K']
    [Field M] [NumberField M]
    [Algebra K L] [Algebra K K'] [Algebra K M] [Algebra L M] [Algebra K' M]
    [IsScalarTower K L M] [IsScalarTower K K' M] [IsGalois K L]
    (hcomp : ∀ x : M, x ∈ Algebra.adjoin K' (Set.range (algebraMap L M)))
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : v.Extension (𝓞 L), Ideal.ramificationIdx' v.asIdeal w.1.asIdeal = 1)
    (𝔳 : v.Extension (𝓞 K')) (𝔴 : 𝔳.1.Extension (𝓞 M))
    (σ : M ≃ₐ[K'] M) (hσ : σ ∈ 𝔴.1.asIdeal.inertia (M ≃ₐ[K'] M)) : σ = 1 := by
  classical
  let σK : M ≃ₐ[K] M := σ.restrictScalars K
  let τ : L ≃ₐ[K] L := σK.restrictNormal L
  have hτ : ∀ y : L, algebraMap L M (τ y) = σ (algebraMap L M y) := fun y =>
    AlgEquiv.restrictNormal_commutes σK L y

  let W : Ideal (𝓞 L) := 𝔴.1.asIdeal.under (𝓞 L)
  have hWv : W.under (𝓞 K) = v.asIdeal := by
    have h1 : W.under (𝓞 K) = 𝔴.1.asIdeal.under (𝓞 K) := Ideal.under_under _
    have h2 : (𝔴.1.asIdeal.under (𝓞 K')).under (𝓞 K) = 𝔴.1.asIdeal.under (𝓞 K) :=
      Ideal.under_under _
    have h3 : 𝔴.1.asIdeal.under (𝓞 K') = 𝔳.1.asIdeal := by
      have := congrArg HeightOneSpectrum.asIdeal 𝔴.2
      simpa only [HeightOneSpectrum.under_asIdeal] using this
    have h4 : 𝔳.1.asIdeal.under (𝓞 K) = v.asIdeal := by
      have := congrArg HeightOneSpectrum.asIdeal 𝔳.2
      simpa only [HeightOneSpectrum.under_asIdeal] using this
    rw [h1, ← h2, h3, h4]
  haveI : W.IsPrime := Ideal.IsPrime.under (𝓞 L) 𝔴.1.asIdeal
  haveI hWover : W.LiesOver v.asIdeal := ⟨hWv.symm⟩
  have hWne : W ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot W
  let w : HeightOneSpectrum (𝓞 L) := ⟨W, inferInstance, hWne⟩
  have hw : w.under (𝓞 K) = v := HeightOneSpectrum.ext_iff.mpr hWv
  have he1 : Ideal.ramificationIdx' v.asIdeal W = 1 := hv ⟨w, hw⟩
  haveI : W.IsMaximal := w.isMaximal
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : Algebra.IsSeparable (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ W) := isSeparable_residueField K L _ _
  have hcard : Nat.card (W.inertia (L ≃ₐ[K] L)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) v.asIdeal W,
      Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal W (L ≃ₐ[K] L),
      ← Ideal.ramificationIdx'_eq_ramificationIdx (p := v.asIdeal) (q := W) v.ne_bot, he1]
  have hτmem : τ ∈ W.inertia (L ≃ₐ[K] L) := by
    intro y
    show algebraMap (𝓞 L) (𝓞 M) (τ • y - y) ∈ 𝔴.1.asIdeal
    have hmap : algebraMap (𝓞 L) (𝓞 M) (τ • y) = σ • algebraMap (𝓞 L) (𝓞 M) y := by
      apply RingOfIntegers.ext
      simp only [coe_algebraMap_ringOfIntegers, coe_smul_ringOfIntegers]
      exact hτ y
    rw [map_sub, hmap]
    exact hσ _
  have hτ1 : τ = 1 := by
    haveI : Subsingleton (W.inertia (L ≃ₐ[K] L)) := (Nat.card_eq_one_iff_unique.mp hcard).1
    have := Subsingleton.elim (⟨τ, hτmem⟩ : W.inertia (L ≃ₐ[K] L)) ⟨1, one_mem _⟩
    exact congrArg Subtype.val this
  have hfix : ∀ y : L, σ (algebraMap L M y) = algebraMap L M y := fun y => by
    rw [← hτ, hτ1, AlgEquiv.one_apply]
  have hle : Algebra.adjoin K' (Set.range (algebraMap L M)) ≤
      AlgHom.equalizer (σ : M →ₐ[K'] M) (AlgHom.id K' M) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨y, rfl⟩
    simpa [AlgHom.mem_equalizer] using hfix y
  ext x
  simpa [AlgHom.mem_equalizer] using hle (hcomp x)

end CMPAux

open CMPAux in

theorem solution
    (K L K' M : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field K'] [NumberField K']
    [Field M] [NumberField M]
    [Algebra K L] [Algebra K K'] [Algebra K M] [Algebra L M] [Algebra K' M]
    [IsScalarTower K L M] [IsScalarTower K K' M] [IsGalois K L]
    (hdisj : Module.finrank K' M = Module.finrank K L)
    (hcomp : ∀ x : M, x ∈ Algebra.adjoin K' (Set.range (algebraMap L M)))
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : v.Extension (𝓞 L), Ideal.ramificationIdx' v.asIdeal w.1.asIdeal = 1)
    (𝔳 : v.Extension (𝓞 K')) (𝔴 : 𝔳.1.Extension (𝓞 M)) :
    Ideal.ramificationIdx' 𝔳.1.asIdeal 𝔴.1.asIdeal = 1 ∧
      Ideal.inertiaDeg' 𝔳.1.asIdeal 𝔴.1.asIdeal ∣ Module.finrank K L := by
  classical
  haveI : IsGalois K' M := isGalois_of_adjoin_range K L K' M hcomp
  haveI : (𝔴.1.asIdeal).IsMaximal := 𝔴.1.isMaximal
  haveI : (𝔳.1.asIdeal).IsMaximal := 𝔳.1.isMaximal
  haveI hPp : (𝔴.1.asIdeal).LiesOver 𝔳.1.asIdeal := ⟨by
    have h := congrArg HeightOneSpectrum.asIdeal 𝔴.2
    simp only [HeightOneSpectrum.under_asIdeal] at h
    exact h.symm⟩
  haveI : Algebra.IsSeparable (𝓞 K' ⧸ 𝔳.1.asIdeal) (𝓞 M ⧸ 𝔴.1.asIdeal) :=
    isSeparable_residueField K' M _ _
  have hI : (𝔴.1.asIdeal).inertia (M ≃ₐ[K'] M) = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_bot]
    exact eq_one_of_mem_inertia K L K' M hcomp v hv 𝔳 𝔴 σ hσ
  have hcard1 : Nat.card ((𝔴.1.asIdeal).inertia (M ≃ₐ[K'] M)) = 1 := by
    rw [hI]; exact Subgroup.card_bot
  refine ⟨?_, ?_⟩
  · rw [Ideal.ramificationIdx'_eq_ramificationIdx (p := 𝔳.1.asIdeal) (q := 𝔴.1.asIdeal) 𝔳.1.ne_bot,
      ← Ideal.ramificationIdxIn_eq_ramificationIdx 𝔳.1.asIdeal 𝔴.1.asIdeal (M ≃ₐ[K'] M),
      ← Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[K'] M) 𝔳.1.asIdeal 𝔴.1.asIdeal, hcard1]
  · have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝔳.1.asIdeal (𝓞 M)
      (M ≃ₐ[K'] M)
    rw [IsGaloisGroup.card_eq_finrank (M ≃ₐ[K'] M) K' M, hdisj,
      Ideal.inertiaDegIn_eq_inertiaDeg 𝔳.1.asIdeal 𝔴.1.asIdeal (M ≃ₐ[K'] M),
      ← Ideal.inertiaDeg'_eq_inertiaDeg (p := 𝔳.1.asIdeal) (q := 𝔴.1.asIdeal)] at hfund
    exact Dvd.intro_left _ ((mul_assoc _ _ _).trans hfund)

end S_IsDedekindDomain_HeightOneSpectrum_ramificationIdx_eq_one_and_inertiaDeg_dvd_of_baseChange_of_unramified
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_ramificationIdx_eq_one_and_inertiaDeg_dvd_of_baseChange_of_unramified (solution)
