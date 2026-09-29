-- Prove2me | solution 1 for LanglandsTunnell.exists_split_place_artinValue4_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/e6b18dad-b883-50f6-aa9f-4c4b5ee89b57

import Definitions.Def_LanglandsTunnell_C4Character
import Theorems.Thm_FrobeniusDensity_statement
import Theorems.Thm_FrobeniusDensity_stabilizer_eq_zpowers_arithFrobAt
import Theorems.Thm_LanglandsTunnell_exists_finset_forall_inertia_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_split_place_artinValue4_ne
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow"

set_option autoImplicit false

open NumberField IsDedekindDomain LanglandsTunnell LanglandsTunnell.P2
open scoped Pointwise

section IndexTwoSplitting

open scoped Pointwise in

private theorem inertia_smul_eq_bot_of_eq_bot {L : Type} [Field L] [NumberField L]
    (τ : L ≃ₐ[ℚ] L) (Q : Ideal (NumberField.RingOfIntegers L))
    (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥) : (τ • Q).inertia (L ≃ₐ[ℚ] L) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hg' : ∀ x : NumberField.RingOfIntegers L, g • x - x ∈ τ • Q :=
    fun x => AddSubgroup.mem_inertia.1 hg x
  have hmem : τ⁻¹ * g * τ ∈ Q.inertia (L ≃ₐ[ℚ] L) := by
    refine AddSubgroup.mem_inertia.2 fun x => ?_
    have hx := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 (hg' (τ • x))
    rw [smul_sub, inv_smul_smul, ← mul_smul, ← mul_smul] at hx
    exact hx
  rw [hI, Subgroup.mem_bot] at hmem
  have hgg : g = τ * (τ⁻¹ * g * τ) * τ⁻¹ := by group
  rw [hmem] at hgg
  simpa using hgg

open scoped Pointwise in

private theorem arithFrobAt_eq_conj_of_smul_eq {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (τ : L ≃ₐ[ℚ] L) (Q₀ Q : Ideal (NumberField.RingOfIntegers L))
    [Q₀.IsPrime] [Finite (NumberField.RingOfIntegers L ⧸ Q₀)]
    [Q.IsPrime] [Finite (NumberField.RingOfIntegers L ⧸ Q)]
    (h : τ • Q₀ = Q) (hI : Q₀.inertia (L ≃ₐ[ℚ] L) = ⊥) :
    arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q = τ * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₀ * τ⁻¹ := by
  subst h
  have h1 : IsArithFrobAt ℤ (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (τ • Q₀)) (τ • Q₀) :=
    IsArithFrobAt.arithFrobAt ℤ (L ≃ₐ[ℚ] L) (τ • Q₀)
  have h2 : IsArithFrobAt ℤ (τ * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₀ * τ⁻¹) (τ • Q₀) :=
    (IsArithFrobAt.arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₀).conj τ
  have h3 := h1.mul_inv_mem_inertia h2
  rw [inertia_smul_eq_bot_of_eq_bot τ Q₀ hI, Subgroup.mem_bot] at h3
  exact mul_inv_eq_one.1 h3

open scoped Pointwise in

private theorem exists_prime_arithFrobAt_eq_pow {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (σ : L ≃ₐ[ℚ] L) (S : Finset ℕ)
    (hS : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∀ Q : Ideal (NumberField.RingOfIntegers L), Q.IsPrime →
      Q.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ) → Q.inertia (L ≃ₐ[ℚ] L) = ⊥) :
    ∃ ℓ : ℕ, ℓ ∉ S ∧ ℓ.Prime ∧
      ∃ (Q : Ideal (NumberField.RingOfIntegers L)) (_ : Q.IsPrime)
        (_ : Q.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ))
        (_ : Finite (NumberField.RingOfIntegers L ⧸ Q)) (k : ℕ),
        k.Coprime (orderOf σ) ∧ arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q = σ ^ k := by
  obtain ⟨ℓ, hℓS, hℓ, hall⟩ := FrobeniusDensity.statement L σ S
  haveI : Fact ℓ.Prime := ⟨hℓ⟩

  obtain ⟨Q, hQmax, hQ⟩ : ∃ Q : Ideal (NumberField.RingOfIntegers L),
      Q.IsMaximal ∧ Q.comap (algebraMap ℤ (NumberField.RingOfIntegers L)) = FrobeniusDensity.ratPrimeIdeal ℓ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral _
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (NumberField.RingOfIntegers L)).injective_int]
          exact bot_le)
  haveI : Q.IsPrime := hQmax.isPrime
  haveI hQℓ : Q.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ) := ⟨hQ.symm⟩
  have hfin : Finite (NumberField.RingOfIntegers L ⧸ Q) :=
    FrobeniusDensity.finite_quotient_of_ne_bot (FrobeniusDensity.ne_bot_of_liesOver_ratPrimeIdeal hℓ)
  obtain ⟨k, hk, hconj⟩ := hall Q inferInstance hQℓ hfin
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj

  haveI : Finite (NumberField.RingOfIntegers L ⧸ c⁻¹ • Q) :=
    FrobeniusDensity.finite_quotient_of_ne_bot
      (FrobeniusDensity.ne_bot_of_liesOver_ratPrimeIdeal (Q := c⁻¹ • Q) hℓ)
  refine ⟨ℓ, hℓS, hℓ, c⁻¹ • Q, inferInstance, inferInstance, inferInstance, k, hk, ?_⟩
  rw [arithFrobAt_eq_conj_of_smul_eq c⁻¹ Q (c⁻¹ • Q) rfl (hS ℓ hℓ hℓS Q inferInstance hQℓ), ← hc]
  group

private theorem isGaloisGroup_ringOfIntegers_fixFld {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (H : Subgroup (L ≃ₐ[ℚ] L)) :
    IsGaloisGroup ↥H (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld H))
      (NumberField.RingOfIntegers L) :=
  IsGaloisGroup.of_isFractionRing _ _ _ ↥(LanglandsTunnell.fixFld H) L

open scoped Pointwise in

private theorem exists_mem_smul_eq_of_under_fixFld_eq {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (H : Subgroup (L ≃ₐ[ℚ] L)) (Q Q' : Ideal (NumberField.RingOfIntegers L)) [Q.IsPrime] [Q'.IsPrime]
    (h : Q.under (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld H))
      = Q'.under (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld H))) :
    ∃ τ ∈ H, τ • Q = Q' := by
  haveI hGG := isGaloisGroup_ringOfIntegers_fixFld (L := L) H
  haveI := hGG.commutes
  haveI := hGG.isInvariant
  haveI : Q'.LiesOver (Q.under (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld H))) := ⟨h⟩
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
    (Q.under (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld H))) Q Q' ↥H
  have hτ' : (τ : L ≃ₐ[ℚ] L) • Q = Q' := hτ
  exact ⟨τ, τ.2, hτ'⟩

private theorem relDeg_eq_one_of_mem {G : Type*} [Group G] [Finite G] (H : Subgroup G) {σ : G}
    (h : σ ∈ H) : LanglandsTunnell.P2.relDeg H σ = 1 := by
  classical
  unfold LanglandsTunnell.P2.relDeg
  rw [Nat.find_eq_iff]
  exact ⟨⟨Nat.one_pos, by rwa [pow_one]⟩, fun n hn hn' => by omega⟩

open scoped Pointwise in

private theorem exists_mem_seedFrob_eq_conj {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (H : Subgroup (L ≃ₐ[ℚ] L)) (Q : Ideal (NumberField.RingOfIntegers L)) [Q.IsPrime]
    [Finite (NumberField.RingOfIntegers L ⧸ Q)] (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥) (ρ : L ≃ₐ[ℚ] L)
    (hF : ρ * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q * ρ⁻¹ ∈ H)
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld H)))
    (hw : (ρ • Q).under (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld H)) = w.asIdeal) :
    ∃ τ ∈ H, LanglandsTunnell.P2.seedFrob H w = τ * (ρ * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q * ρ⁻¹) * τ⁻¹ := by
  obtain ⟨τ, hτ, hτQ⟩ := exists_mem_smul_eq_of_under_fixFld_eq H (ρ • Q) (LanglandsTunnell.P2.primeOver H w)
    (hw.trans (LanglandsTunnell.P2.under_primeOver H w).symm)
  rw [← mul_smul] at hτQ
  have hfrob : arithFrobAt ℤ (L ≃ₐ[ℚ] L) (LanglandsTunnell.P2.primeOver H w)
      = τ * (ρ * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q * ρ⁻¹) * τ⁻¹ := by
    rw [arithFrobAt_eq_conj_of_smul_eq (τ * ρ) Q _ hτQ hI]
    group
  have hmem : arithFrobAt ℤ (L ≃ₐ[ℚ] L) (LanglandsTunnell.P2.primeOver H w) ∈ H := by
    rw [hfrob]
    exact H.mul_mem (H.mul_mem hτ hF) (H.inv_mem hτ)
  refine ⟨τ, hτ, ?_⟩
  unfold LanglandsTunnell.P2.seedFrob
  rw [relDeg_eq_one_of_mem H hmem, pow_one, hfrob]

private theorem isScalarTower_ringOfIntegers_fixFld {L : Type} [Field L] [NumberField L]
    (E K : IntermediateField ℚ L) [Algebra ↥E ↥K] [IsScalarTower ↥E ↥K L] :
    IsScalarTower (NumberField.RingOfIntegers ↥E) (NumberField.RingOfIntegers ↥K)
      (NumberField.RingOfIntegers L) := by
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  apply IsFractionRing.injective (NumberField.RingOfIntegers L) L
  rw [← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥E) (NumberField.RingOfIntegers L) L,
    ← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥K) (NumberField.RingOfIntegers L) L,
    IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥E) ↥E L,
    IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥K) ↥K L,
    ← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥E) (NumberField.RingOfIntegers ↥K) ↥K,
    IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥E) ↥E ↥K,
    ← IsScalarTower.algebraMap_apply ↥E ↥K L]

private theorem under_int_eq_ratPrimeIdeal {K : Type*} [Field K] [NumberField K]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hw : ((ℓ : ℕ) : NumberField.RingOfIntegers K) ∈ w.asIdeal) :
    w.asIdeal.under ℤ = FrobeniusDensity.ratPrimeIdeal ℓ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  refine ((Int.ideal_span_isMaximal_of_prime ℓ).eq_of_le (Ideal.IsPrime.under ℤ w.asIdeal).ne_top ?_).symm
  show Ideal.span {((ℓ : ℕ) : ℤ)} ≤ w.asIdeal.under ℤ
  rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap, map_natCast]
  exact hw

open scoped Pointwise in

private theorem exists_split_pair {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (H N : Subgroup (L ≃ₐ[ℚ] L))
    [Algebra ↥(LanglandsTunnell.fixFld N) ↥(LanglandsTunnell.fixFld H)]
    [IsScalarTower ↥(LanglandsTunnell.fixFld N) ↥(LanglandsTunnell.fixFld H) L]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (Q : Ideal (NumberField.RingOfIntegers L)) [Q.IsPrime]
    [Q.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ)] [Finite (NumberField.RingOfIntegers L ⧸ Q)]
    (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥)
    (hstab : MulAction.stabilizer (L ≃ₐ[ℚ] L) Q ≤ H)
    (s : L ≃ₐ[ℚ] L) (hsN : s ∈ N) (hsH : s ∉ H)
    (hsF : s * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q * s⁻¹ ∈ H)
    {A : Type*} [CommGroup A] (χ : ↥H →* A) :
    ∃ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld N)),
      v.asIdeal.under ℤ = FrobeniusDensity.ratPrimeIdeal ℓ ∧
      ∃ 𝔓₁ 𝔓₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld H)),
        𝔓₁ ≠ 𝔓₂ ∧ 𝔓₁.under (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld N)) = v ∧
        𝔓₂.under (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld N)) = v ∧
        ∃ (hF : arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q ∈ H)
          (hF' : s * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q * s⁻¹ ∈ H),
          χ ⟨LanglandsTunnell.P2.seedFrob H 𝔓₁, LanglandsTunnell.P2.seedFrob_mem H 𝔓₁⟩
              = χ ⟨arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q, hF⟩ ∧
          χ ⟨LanglandsTunnell.P2.seedFrob H 𝔓₂, LanglandsTunnell.P2.seedFrob_mem H 𝔓₂⟩
              = χ ⟨s * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q * s⁻¹, hF'⟩ := by
  haveI := isScalarTower_ringOfIntegers_fixFld (L := L) (LanglandsTunnell.fixFld N) (LanglandsTunnell.fixFld H)
  haveI hGN := isGaloisGroup_ringOfIntegers_fixFld (L := L) N
  haveI := hGN.commutes
  have hF : arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q ∈ H :=
    hstab (IsArithFrobAt.arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q).mem_stabilizer
  have hQ : Q ≠ ⊥ := FrobeniusDensity.ne_bot_of_liesOver_ratPrimeIdeal hℓ
  have hsQ : s • Q ≠ ⊥ := fun h => hQ (by
    rw [← inv_smul_smul s Q, h, Ideal.pointwise_smul_def, Ideal.map_bot])
  haveI : Finite (NumberField.RingOfIntegers L ⧸ s • Q) := FrobeniusDensity.finite_quotient_of_ne_bot hsQ

  let QL : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) := ⟨Q, inferInstance, hQ⟩
  let QsL : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) := ⟨s • Q, inferInstance, hsQ⟩

  have hℓQ : ((ℓ : ℕ) : NumberField.RingOfIntegers L) ∈ Q := by
    have h := (Ideal.LiesOver.over (P := Q) (p := FrobeniusDensity.ratPrimeIdeal ℓ)).symm
    have hmem : ((ℓ : ℕ) : ℤ) ∈ Q.under ℤ := by
      rw [h]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast] at hmem
    exact hmem
  have hℓv : ((ℓ : ℕ) : NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld N))
      ∈ (QL.under (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld N))).asIdeal := by
    show _ ∈ Q.under _
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hℓQ

  obtain ⟨τ₁, hτ₁, hseed₁⟩ := exists_mem_seedFrob_eq_conj H Q hI 1 (by simpa using hF)
    (QL.under (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld H))) (by rw [one_smul]; rfl)
  simp only [one_mul, inv_one, mul_one] at hseed₁
  obtain ⟨τ₂, hτ₂, hseed₂⟩ := exists_mem_seedFrob_eq_conj H Q hI s hsF
    (QsL.under (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld H))) rfl
  refine ⟨QL.under _, under_int_eq_ratPrimeIdeal _ hℓ hℓv, QL.under _, QsL.under _, ?_, ?_, ?_, hF, hsF, ?_, ?_⟩
  ·
    intro h
    have h' : Q.under (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld H))
        = (s • Q).under (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld H)) :=
      congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h
    obtain ⟨τ, hτ, hτQ⟩ := exists_mem_smul_eq_of_under_fixFld_eq H Q (s • Q) h'
    have hfix : (τ⁻¹ * s) • Q = Q := by rw [mul_smul, ← hτQ, inv_smul_smul]
    have hmem : τ⁻¹ * s ∈ H := hstab (MulAction.mem_stabilizer_iff.2 hfix)
    have hs : s ∈ H := by
      have := H.mul_mem hτ hmem
      rwa [mul_inv_cancel_left] at this
    exact hsH hs
  · refine IsDedekindDomain.HeightOneSpectrum.ext ?_
    show (Q.under (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld H))).under _ = Q.under _
    exact Ideal.under_under Q
  · refine IsDedekindDomain.HeightOneSpectrum.ext ?_
    show ((s • Q).under (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld H))).under _ = Q.under _
    rw [Ideal.under_under]
    exact Ideal.under_smul (A := NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld N))
      (P := Q) (g := (⟨s, hsN⟩ : ↥N))
  · have hx : (⟨LanglandsTunnell.P2.seedFrob H (QL.under _), LanglandsTunnell.P2.seedFrob_mem H _⟩ : ↥H)
        = ⟨τ₁, hτ₁⟩ * ⟨arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q, hF⟩ * ⟨τ₁, hτ₁⟩⁻¹ :=
      Subtype.ext (by simpa using hseed₁)
    rw [hx, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  · have hx : (⟨LanglandsTunnell.P2.seedFrob H (QsL.under _), LanglandsTunnell.P2.seedFrob_mem H _⟩ : ↥H)
        = ⟨τ₂, hτ₂⟩ * ⟨s * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q * s⁻¹, hsF⟩ * ⟨τ₂, hτ₂⟩⁻¹ :=
      Subtype.ext (by simpa using hseed₂)
    rw [hx, map_mul, map_mul, map_inv, mul_inv_cancel_comm]

end IndexTwoSplitting

section ConjugationBricks

private def Jlift : Matrix (Fin 2) (Fin 2) (ℤ√(-2)) := !![⟨-1, 1⟩, ⟨2, 0⟩; ⟨0, 1⟩, ⟨1, -1⟩]

private theorem Jlift_mem_P16 : Jlift ∈ LanglandsTunnell.Lift48.P16 := by decide +kernel

private theorem Jlift_det : Jlift.det = 1 := by
  rw [Matrix.det_fin_two]; decide

private theorem Jlift_mul_Tlift :
    Jlift * FLT.ExplicitLift.Tlift = LanglandsTunnell.Lift48.pw FLT.ExplicitLift.Tlift 3 * Jlift := by
  decide +kernel

private noncomputable def jbarGL : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Jlift.map FLT.ExplicitLift.red) (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Jlift_det, map_one]; exact one_ne_zero)

private theorem val_jbarGL :
    ((jbarGL : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))
      = Jlift.map FLT.ExplicitLift.red :=
  rfl

private theorem jbarGL_mul_tbarGL :
    jbarGL * LanglandsTunnell.P2.tbarGL = LanglandsTunnell.P2.tbarGL ^ 3 * jbarGL := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, LanglandsTunnell.P2.val_tbarGL_pow, val_jbarGL,
    LanglandsTunnell.P2.val_tbarGL, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← Matrix.map_mul,
    ← Matrix.map_mul, Jlift_mul_Tlift, LanglandsTunnell.Lift48.pw_eq_pow]

private theorem exists_conj_gammaT_eq_pow_three {L : Type} [Field L] [NumberField L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    ∃ s : L ≃ₐ[ℚ] L, s ∈ LanglandsTunnell.sylowH e ∧ s ∈ LanglandsTunnell.detKer e ∧
      s * LanglandsTunnell.P2.gammaT e * s⁻¹ = LanglandsTunnell.P2.gammaT e ^ 3 := by
  refine ⟨e.symm jbarGL, ⟨Jlift, Jlift_mem_P16, ?_⟩, ?_, ?_⟩
  · rw [MulEquiv.apply_symm_apply]; rfl
  · rw [LanglandsTunnell.mem_detKer_iff, MulEquiv.apply_symm_apply, val_jbarGL, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det, Jlift_det, map_one]
  · apply e.injective
    rw [map_mul, map_mul, map_inv, map_pow, MulEquiv.apply_symm_apply, LanglandsTunnell.P2.e_gammaT,
      mul_inv_eq_iff_eq_mul, jbarGL_mul_tbarGL]

private theorem exists_mem_sylowH_conj_gammaT {L : Type} [Field L] [NumberField L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    ∃ s ∈ LanglandsTunnell.sylowH e, s ∉ LanglandsTunnell.P2.c8H e ∧
      s * LanglandsTunnell.P2.gammaT e * s⁻¹ = LanglandsTunnell.P2.gammaT e ^ 3 := by
  obtain ⟨s, hsS, -, hconj⟩ := exists_conj_gammaT_eq_pow_three e
  refine ⟨s, hsS, fun hsC => ?_, hconj⟩
  obtain ⟨k, hk⟩ := LanglandsTunnell.P2.exists_pow_gammaT_eq e hsC
  have hcomm : s * LanglandsTunnell.P2.gammaT e * s⁻¹ = LanglandsTunnell.P2.gammaT e := by
    rw [← hk, ← pow_succ, pow_succ', mul_inv_cancel_right]
  have h2 : LanglandsTunnell.P2.gammaT e ^ 2 = 1 := by
    have h := hconj
    rw [hcomm] at h
    calc LanglandsTunnell.P2.gammaT e ^ 2
        = (LanglandsTunnell.P2.gammaT e)⁻¹ * LanglandsTunnell.P2.gammaT e ^ 3 := by group
      _ = 1 := by rw [← h, inv_mul_cancel]
  have hdvd := orderOf_dvd_of_pow_eq_one h2
  rw [LanglandsTunnell.P2.orderOf_gammaT] at hdvd
  omega

end ConjugationBricks

section QuarticBrick

private theorem exists_mem_quatH_conj_gammaT_sq {L : Type} [Field L] [NumberField L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    ∃ s : L ≃ₐ[ℚ] L, s ∈ LanglandsTunnell.quatH e ∧ s ∉ LanglandsTunnell.P2.c4H e ∧
      s * LanglandsTunnell.P2.gammaT e ^ 2 * s⁻¹ = (LanglandsTunnell.P2.gammaT e ^ 2)⁻¹ := by
  obtain ⟨s, hsS, hsD, hconj⟩ := exists_conj_gammaT_eq_pow_three e
  have h8 : LanglandsTunnell.P2.gammaT e ^ 8 = 1 := by
    rw [← LanglandsTunnell.P2.orderOf_gammaT e]; exact pow_orderOf_eq_one _
  have hsq : s * LanglandsTunnell.P2.gammaT e ^ 2 * s⁻¹ = (LanglandsTunnell.P2.gammaT e ^ 2)⁻¹ := by
    rw [← conj_pow, hconj, ← pow_mul, eq_inv_iff_mul_eq_one, ← pow_add]
    exact h8
  refine ⟨s, ?_, fun hsC => ?_, hsq⟩
  · show s ∈ LanglandsTunnell.sylowH e ⊓ LanglandsTunnell.detKer e
    exact Subgroup.mem_inf.2 ⟨hsS, hsD⟩
  · obtain ⟨k, hk⟩ := (LanglandsTunnell.P2.mem_c4H_iff e s).1 hsC
    have hcomm : s * LanglandsTunnell.P2.gammaT e ^ 2 * s⁻¹ = LanglandsTunnell.P2.gammaT e ^ 2 := by
      rw [← hk, (Commute.zpow_self (LanglandsTunnell.P2.gammaT e ^ 2) k).eq, mul_inv_cancel_right]
    have h4 : (LanglandsTunnell.P2.gammaT e ^ 2) ^ 2 = 1 := by
      have h := hsq
      rw [hcomm, eq_inv_iff_mul_eq_one, ← pow_two] at h
      exact h
    have hdvd := orderOf_dvd_of_pow_eq_one h4
    rw [LanglandsTunnell.P2.orderOf_gammaT_sq] at hdvd
    omega

end QuarticBrick

private theorem quat_frobTransport {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (σ : L ≃ₐ[ℚ] L) (S : Finset ℕ)
    (hS : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∀ Q : Ideal (𝓞 L), Q.IsPrime →
      Q.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ) → Q.inertia (L ≃ₐ[ℚ] L) = ⊥) :
    ∃ ℓ : ℕ, ℓ ∉ S ∧ ℓ.Prime ∧
      ∃ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime) (_ : Q.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ))
        (_ : Finite (𝓞 L ⧸ Q)) (k : ℕ),
        k.Coprime (orderOf σ) ∧ arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q = σ ^ k :=
  exists_prime_arithFrobAt_eq_pow σ S hS

private theorem quat_splitPair {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) {ζ : ℂ} (hζ : ζ ^ 4 = -1)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ)] [Finite (𝓞 L ⧸ Q)]
    (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥) (hstab : MulAction.stabilizer (L ≃ₐ[ℚ] L) Q ≤ c4H e)
    (s : L ≃ₐ[ℚ] L) (hsN : s ∈ quatH e) (hsH : s ∉ c4H e)
    (hsF : s * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q * s⁻¹ ∈ c4H e) :
    ∃ v : HeightOneSpectrum (𝓞 ↥(fixFld (quatH e))),
      v.asIdeal.under ℤ = FrobeniusDensity.ratPrimeIdeal ℓ ∧
      ∃ 𝔓₁ 𝔓₂ : HeightOneSpectrum (𝓞 ↥(fixFld (c4H e))),
        𝔓₁ ≠ 𝔓₂ ∧ 𝔓₁.under (𝓞 ↥(fixFld (quatH e))) = v ∧ 𝔓₂.under (𝓞 ↥(fixFld (quatH e))) = v ∧
        ∃ (hF : arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q ∈ c4H e)
          (hF' : s * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q * s⁻¹ ∈ c4H e),
          artinValue4 e hζ 𝔓₁ = chiGal4 e hζ ⟨arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q, hF⟩ ∧
          artinValue4 e hζ 𝔓₂ = chiGal4 e hζ ⟨s * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q * s⁻¹, hF'⟩ :=
  exists_split_pair (c4H e) (quatH e) hℓ Q hI hstab s hsN hsH hsF (chiGal4 e hζ)

private theorem quat_invBrick {L : Type} [Field L] [NumberField L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    ∃ s : L ≃ₐ[ℚ] L, s ∈ quatH e ∧ s ∉ c4H e ∧ s * gammaT e ^ 2 * s⁻¹ = (gammaT e ^ 2)⁻¹ :=
  exists_mem_quatH_conj_gammaT_sq e

private noncomputable def quat_ratUnder {L : Type} [Field L] [NumberField L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (w : HeightOneSpectrum (𝓞 ↥(fixFld (quatH e)))) : ℕ :=
  Ideal.absNorm (w.asIdeal.under ℤ)

private theorem quat_pow_ne_inv {G : Type} [Group G] (σ : G) (hσ : orderOf σ = 4) (k : ℕ)
    (hk : k.Coprime 4) : σ ^ k ≠ (σ ^ k)⁻¹ := by
  intro h
  have h2 : (σ ^ k) ^ 2 = 1 := by
    rw [pow_two]; nth_rewrite 2 [h]; exact mul_inv_cancel (σ ^ k)
  rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one, hσ] at h2
  obtain ⟨c, hc⟩ := h2
  have h2k : 2 ∣ k := ⟨c, by omega⟩
  have hg : 2 ∣ Nat.gcd k 4 := Nat.dvd_gcd h2k (by norm_num)
  rw [Nat.Coprime.gcd_eq_one hk] at hg
  omega

theorem solution
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) {ζ : ℂ} (hζ : ζ ^ 4 = -1) :
    ∀ S : Finset (HeightOneSpectrum (𝓞 ↥(fixFld (quatH e)))), ∃ v ∉ S,
      ∃ 𝔓₁ 𝔓₂ : HeightOneSpectrum (𝓞 ↥(fixFld (c4H e))),
      𝔓₁ ≠ 𝔓₂ ∧ 𝔓₁.under (𝓞 ↥(fixFld (quatH e))) = v ∧ 𝔓₂.under (𝓞 ↥(fixFld (quatH e))) = v ∧
      artinValue4 e hζ 𝔓₁ ≠ artinValue4 e hζ 𝔓₂ := by
  intro S
  obtain ⟨B, hB⟩ := LanglandsTunnell.exists_finset_forall_inertia_eq_bot L
  obtain ⟨s, hsN, hsH, hinv⟩ := quat_invBrick e
  obtain ⟨ℓ, hℓS, hℓ, Q, hQp, hQl, hQfin, k, hk, hF⟩ :=
    quat_frobTransport (gammaT e ^ 2) (S.image (quat_ratUnder e) ∪ B)
      (fun ℓ hℓ hℓS Q hQ hQl => hB hℓ (fun hℓB => hℓS (Finset.mem_union_right _ hℓB)) Q hQ hQl)
  have hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥ :=
    hB hℓ (fun hℓB => hℓS (Finset.mem_union_right _ hℓB)) Q hQp hQl
  have hstab : MulAction.stabilizer (L ≃ₐ[ℚ] L) Q ≤ c4H e := by
    rw [FrobeniusDensity.stabilizer_eq_zpowers_arithFrobAt hℓ Q hI, hF]
    exact Subgroup.zpowers_le.2 (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k)
  have hsF : s * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q * s⁻¹ ∈ c4H e := by
    rw [hF, ← conj_pow, hinv]
    exact Subgroup.pow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) k
  obtain ⟨v, hvℓ, 𝔓₁, 𝔓₂, hne, h₁, h₂, hF₁, hF₂, hval₁, hval₂⟩ :=
    quat_splitPair e hζ hℓ Q hI hstab s hsN hsH hsF
  refine ⟨v, ?_, 𝔓₁, 𝔓₂, hne, h₁, h₂, ?_⟩
  · intro hvS
    apply hℓS
    refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨v, hvS, ?_⟩)
    simp [quat_ratUnder, hvℓ, FrobeniusDensity.ratPrimeIdeal, Ideal.absNorm_span_singleton]
  · rw [hval₁, hval₂]
    intro heq
    have hsub : arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q = s * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q * s⁻¹ :=
      congrArg Subtype.val (chiGal4_injective e hζ heq)
    rw [hF, ← conj_pow, hinv, inv_pow] at hsub
    exact quat_pow_ne_inv (gammaT e ^ 2) (orderOf_gammaT_sq e) k
      (by simpa [orderOf_gammaT_sq e] using hk) hsub

end S_LanglandsTunnell_exists_split_place_artinValue4_ne
end P2MW
export P2MW.S_LanglandsTunnell_exists_split_place_artinValue4_ne (solution)
