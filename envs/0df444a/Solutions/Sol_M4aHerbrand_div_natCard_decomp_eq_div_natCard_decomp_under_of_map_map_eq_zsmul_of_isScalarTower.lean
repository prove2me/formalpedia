-- Prove2me | solution 1 for M4aHerbrand.div_natCard_decomp_eq_div_natCard_decomp_under_of_map_map_eq_zsmul_of_isScalarTower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/cecbfe6e-f08d-5dad-99be-3762850f977f

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_map_decomp_map_ideles_eq_map_map_decomp_under_of_isScalarTower
import Theorems.Thm_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion
import Theorems.Thm_NumberField_PlaceDecomp_mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv
import Theorems.Thm_NumberField_PlaceDecomp_exists_localLevel_ringEquiv_adicCompletion_tower
import Theorems.Thm_NumberField_PlaceDecomp_exists_restrict_decomp_surjective_of_tower
import Theorems.Thm_NumberField_PlaceDecomp_exists_isLocalFundamentalClass_map_eq_natCard_ker_smul_of_tower
import Theorems.Thm_NumberField_PlaceDecomp_zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass
import Theorems.Thm_ExtCitation_LocalLevel_isSolvable_of_faithfulSMul_of_padic
import Theorems.Thm_NumberField_PlaceDecomp_faithfulSMul_decomp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_div_natCard_decomp_eq_div_natCard_decomp_under_of_map_map_eq_zsmul_of_isScalarTower
p2m_attr_erase "instance" "ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
p2m_open "CategoryTheory NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_div_natCard_decomp_eq_div_natCard_decomp_under_of_map_map_eq_zsmul_of_isScalarTower.M4aHerbrand"
open scoped NumberField.PlaceDecomp

namespace M4aHerbrand
p2m_export "M4aHerbrand" "finPart GenuineDescent.genuineBaseChange map_decomp_map_ideles_eq_map_map_decomp_under_of_isScalarTower"
namespace InfLocalReadProof
p2m_open "M4aHerbrand"

open NumberField.PlaceDecomp

variable {E F M : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra E F] [Algebra E M] [Algebra F M] [IsScalarTower E F M]

noncomputable def iDOf (W : HeightOneSpectrum (𝓞 M))
    (r : ↥(decomp E M W) →* ↥(decomp E F (W.under (𝓞 F))))
    (hrsemi : ∀ (σ : ↥(decomp E M W)) (x : (W.under (𝓞 F)).adicCompletion F),
      HeightOneSpectrum.Extension.adicCompletionSemialgHom F M (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 M)) (r σ • x) =
        σ • HeightOneSpectrum.Extension.adicCompletionSemialgHom F M (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 M)) x) :
    Rep.res r (Rep.ofMulDistribMulAction (↥(decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ) ⟶
      Rep.ofMulDistribMulAction (↥(decomp E M W)) (W.adicCompletion M)ˣ :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (Units.map
      (HeightOneSpectrum.Extension.adicCompletionSemialgHom F M (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 M))).toMonoidHom)).toIntLinearMap,
    fun g => LinearMap.ext fun a => by
      change Additive.ofMul (Units.map _ ((r g) • (Additive.toMul : _ ≃ ((W.under (𝓞 F)).adicCompletion F)ˣ) a))
        = Additive.ofMul (g • Units.map _ ((Additive.toMul : _ ≃ ((W.under (𝓞 F)).adicCompletion F)ˣ) a))
      congr 1
      apply Units.ext
      rw [coe_smul_units, Units.coe_map, Units.coe_map, coe_smul_units]
      exact hrsemi g _⟩

theorem iDOf_apply (W : HeightOneSpectrum (𝓞 M))
    (r : ↥(decomp E M W) →* ↥(decomp E F (W.under (𝓞 F)))) (hrsemi) (x : ((W.under (𝓞 F)).adicCompletion F)ˣ) :
    ((Additive.toMul ((iDOf W r hrsemi).hom (Additive.ofMul x)) : (W.adicCompletion M)ˣ) : W.adicCompletion M) =
      HeightOneSpectrum.Extension.adicCompletionSemialgHom F M (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 M)) (x : (W.under (𝓞 F)).adicCompletion F) :=
  rfl

theorem faithfulSMul_of_bridge {K : Type} [Field K] [NumberField K] [Algebra E K] (w : HeightOneSpectrum (𝓞 K))
    {q : ℕ} [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [MulSemiringAction (↥(decomp E K w)) L']
    (Φ : w.adicCompletion K ≃+* L') (hΦ : ∀ (g : ↥(decomp E K w)) (y : w.adicCompletion K), Φ (g • y) = g • Φ y) :
    FaithfulSMul (↥(decomp E K w)) L' := by
  haveI := NumberField.PlaceDecomp.faithfulSMul_decomp E K w
  refine ⟨fun {g₁ g₂} h => ?_⟩
  apply FaithfulSMul.eq_of_smul_eq_smul (α := w.adicCompletion K)
  intro y
  apply Φ.injective
  rw [hΦ, hΦ, h]

theorem addCircle_div_eq_div {a b m : ℤ} {B k : ℕ} (hB : B ≠ 0) (hk : k ≠ 0) (hm : a - b * k = ((k * B : ℕ) : ℤ) * m) :
    (((a : ℚ) / ((k * B : ℕ) : ℚ) : ℚ) : AddCircle (1 : ℚ)) = (((b : ℚ) / (B : ℚ) : ℚ) : AddCircle (1 : ℚ)) := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
  refine ⟨m, ?_⟩
  have hB' : (B : ℚ) ≠ 0 := by exact_mod_cast hB
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk
  have hm' : (a : ℚ) - b * k = (k * B) * m := by exact_mod_cast hm
  rw [zsmul_eq_mul, mul_one, Nat.cast_mul, eq_comm, div_sub_div _ _ (mul_ne_zero hk' hB') hB',
    div_eq_iff (mul_ne_zero (mul_ne_zero hk' hB') hB')]
  linear_combination (B : ℚ) * hm'

end M4aHerbrand.InfLocalReadProof

open M4aHerbrand.InfLocalReadProof NumberField.PlaceDecomp in

theorem solution
    (E F M : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra E F] [Algebra E M] [Algebra F M] [IsScalarTower E F M] [IsGalois E F] [IsGalois E M]
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ] [MulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ]

    (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (F ≃ₐ[E] F))
    (hι : ∀ (g : M ≃ₐ[E] M) (x : F), algebraMap F M (ι (QuotientGroup.mk g) x) = g (algebraMap F M x))

    (J : Rep.res (ι.toMonoidHom.comp (QuotientGroup.mk' S)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
          Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ)
    (hJ : ∀ x : (AdeleRing (𝓞 F) F)ˣ, J.hom (Additive.ofMul x) =
        Additive.ofMul (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange F M).β.toMonoidHom x))

    (W : HeightOneSpectrum (𝓞 M))
    (prG : Rep.res (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ)
    (hprG : ∀ x : (AdeleRing (𝓞 F) F)ˣ, prG.hom (Additive.ofMul x) = Additive.ofMul (finPart (W.under (𝓞 F)) x))
    (prM : Rep.res (NumberField.PlaceDecomp.decomp E M W).subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ)
    (hprM : ∀ x : (AdeleRing (𝓞 M) M)ˣ, prM.hom (Additive.ofMul x) = Additive.ofMul (finPart W x))
    (y : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2))

    (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) L']
    [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (↥L')ˣ]
    (Φ : (W.under (𝓞 F)).adicCompletion F ≃+* L')
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (y : ℚ_[q]), g • algebraMap ℚ_[q] L' y = algebraMap ℚ_[q] L' y)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (y : (↥L')ˣ), ((g • y : (↥L')ˣ) : L') = g • (y : L'))
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (y : (W.under (𝓞 F)).adicCompletion F), Φ (g • y) = g • Φ y)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
    (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) K₀)
    (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (↥L')ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ)
    (_ : ∀ y : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : ((W.under (𝓞 F)).adicCompletion F)ˣ) : (W.under (𝓞 F)).adicCompletion F) = Φ.symm (y : L'))
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (↥L')ˣ))
    (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) K₀ u)
    (n : ℤ)
    (_ : (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).subtype prG 2).hom y =
        n • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) θ 2).hom u)

    (qM : ℕ) [Fact qM.Prime] (LM : IntermediateField ℚ_[qM] (PadicAlgCl qM)) [FiniteDimensional ℚ_[qM] LM]
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E M W)) LM]
    [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (↥LM)ˣ]
    (ΦM : W.adicCompletion M ≃+* LM)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E M W)) (y : ℚ_[qM]), g • algebraMap ℚ_[qM] LM y = algebraMap ℚ_[qM] LM y)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E M W)) (y : (↥LM)ˣ), ((g • y : (↥LM)ˣ) : LM) = g • (y : LM))
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E M W)) (y : W.adicCompletion M), ΦM (g • y) = g • ΦM y)
    (KM : IntermediateField ℚ_[qM] (PadicAlgCl qM)) [FiniteDimensional ℚ_[qM] KM]
    (_ : ExtCitation.LocalLevel.IsBase qM LM (↥(NumberField.PlaceDecomp.decomp E M W)) KM)
    (θM : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (↥LM)ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ)
    (_ : ∀ y : (↥LM)ˣ, ((Additive.toMul (θM.hom (Additive.ofMul y)) : (W.adicCompletion M)ˣ) : W.adicCompletion M) = ΦM.symm (y : LM))
    (uM : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (↥LM)ˣ))
    (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass qM LM (↥(NumberField.PlaceDecomp.decomp E M W)) KM uM)
    (nM : ℤ)
    (_ : (groupCohomology.map (NumberField.PlaceDecomp.decomp E M W).subtype prM 2).hom
          ((groupCohomology.map (ι.toMonoidHom.comp (QuotientGroup.mk' S)) J 2).hom y) =
        nM • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E M W)) θM 2).hom uM) :
    (((nM : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E M W) : ℚ) : ℚ) : AddCircle (1 : ℚ)) =
      (((n : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) : ℚ) : ℚ) : AddCircle (1 : ℚ)) := by
  rename_i _ _ _ _ hqalg hucompat hΦ _ hK₀ hθ hu hn _ _ _ _ hqMalg huMcompat hΦM _ hKM hθM huM hnM

  obtain ⟨r, hrsurj, hrres, -, -, hrsemi⟩ := NumberField.PlaceDecomp.exists_restrict_decomp_surjective_of_tower E F M W
  have hr : ∀ (σ : ↥(decomp E M W)) (x : F),
      algebraMap F M (((r σ : ↥(decomp E F (W.under (𝓞 F)))) : F ≃ₐ[E] F) x) = (σ : M ≃ₐ[E] M) (algebraMap F M x) := by
    intro σ x
    rw [hrres σ]
    exact AlgEquiv.restrictNormal_commutes (σ : M ≃ₐ[E] M) F x
  let iD := iDOf W r hrsemi
  have hiD := iDOf_apply W r hrsemi

  have hcoord := M4aHerbrand.map_decomp_map_ideles_eq_map_map_decomp_under_of_isScalarTower E F M S ι hι J hJ W prG hprG prM hprM
    r hr iD hiD 2 y

  obtain ⟨qT, hqT, LT, LT'', hle, fdT, fdT'', msaT, fT, mdaT, msaT'', fT'', mdaT'', ΦT, ΦT'', hΦT, hΦT'', hqGT, hqGT'', hcT, hcT'',
    hcompatT, hqTmem⟩ := NumberField.PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion_tower E F M W
  haveI := hqT; haveI := fdT; haveI := fdT''
  letI := msaT; letI := mdaT; letI := msaT''; letI := mdaT''; haveI := fT; haveI := fT''
  have hsolv : Group.IsSolvable ↥(decomp E M W) := ExtCitation.LocalLevel.isSolvable_of_faithfulSMul_of_padic qT LT'' _ hqGT''
  have hsolv₁ : Group.IsSolvable ↥(decomp E F (W.under (𝓞 F))) := ExtCitation.LocalLevel.isSolvable_of_faithfulSMul_of_padic qT LT _ hqGT

  obtain ⟨K₀T, fdK, θT, θT'', uT, uT'', hBT, hBT'', hθT, hθT'', huT, huT'', hinf, hcardmul⟩ :=
    NumberField.PlaceDecomp.exists_isLocalFundamentalClass_map_eq_natCard_ker_smul_of_tower E F M W hsolv hsolv₁ r hr iD hiD
      qT LT LT'' hle ΦT ΦT'' hΦT hΦT'' hqGT hqGT'' hcT hcT'' hcompatT
  haveI := fdK

  have hqmem : ((q : ℕ) : 𝓞 F) ∈ (W.under (𝓞 F)).asIdeal :=
    (NumberField.PlaceDecomp.mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv F (W.under (𝓞 F)) q L' Φ).2
  have hqMmem : ((qM : ℕ) : 𝓞 M) ∈ W.asIdeal :=
    (NumberField.PlaceDecomp.mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv M W qM LM ΦM).2
  have hqTmem₁ : ((qT : ℕ) : 𝓞 F) ∈ (W.under (𝓞 F)).asIdeal := by
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hqTmem
  haveI := faithfulSMul_of_bridge (E := E) (W.under (𝓞 F)) L' Φ hΦ
  haveI := faithfulSMul_of_bridge (E := E) W LM ΦM hΦM

  have hswap₁ := NumberField.PlaceDecomp.map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion E F (W.under (𝓞 F))
    q hqmem L' Φ hqalg hucompat hΦ K₀ hK₀ θ hθ u hu qT hqTmem₁ LT ΦT hqGT hcT hΦT K₀T hBT θT hθT uT huT
  have hswap := NumberField.PlaceDecomp.map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion E M W
    qM hqMmem LM ΦM hqMalg huMcompat hΦM KM hKM θM hθM uM huM qT hqTmem LT'' ΦT'' hqGT'' hcT'' hΦT'' K₀T hBT'' θT'' hθT'' uT'' huT''

  have e1 : nM • (groupCohomology.map (MonoidHom.id ↥(decomp E M W)) θT'' 2).hom uT'' =
      (groupCohomology.map r iD 2).hom ((groupCohomology.map (decomp E F (W.under (𝓞 F))).subtype prG 2).hom y) := by
    rw [← hswap, ← hnM, hcoord]
  have e2 : (groupCohomology.map r iD 2).hom ((groupCohomology.map (decomp E F (W.under (𝓞 F))).subtype prG 2).hom y) =
      (n * (Nat.card ↥r.ker : ℤ)) • (groupCohomology.map (MonoidHom.id ↥(decomp E M W)) θT'' 2).hom uT'' := by
    rw [hn, map_zsmul, hswap₁, hinf, mul_zsmul, natCast_zsmul]
  have hzero : (nM - n * (Nat.card ↥r.ker : ℤ)) •
      (groupCohomology.map (MonoidHom.id ↥(decomp E M W)) θT'' 2).hom uT'' = 0 := by
    rw [sub_zsmul, e1, e2, add_neg_cancel]

  obtain ⟨m, hm⟩ := (NumberField.PlaceDecomp.zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass E M W hsolv
    qT LT'' ΦT'' hqGT'' hcT'' hΦT'' K₀T hBT'' θT'' hθT'' uT'' huT'' _).1 hzero
  rw [hcardmul] at hm ⊢

  exact addCircle_div_eq_div (Nat.card_pos (α := ↥(decomp E F (W.under (𝓞 F))))).ne' (Nat.card_pos (α := ↥r.ker)).ne' hm

end S_M4aHerbrand_div_natCard_decomp_eq_div_natCard_decomp_under_of_map_map_eq_zsmul_of_isScalarTower
end P2MW
export P2MW.S_M4aHerbrand_div_natCard_decomp_eq_div_natCard_decomp_under_of_map_map_eq_zsmul_of_isScalarTower (solution)
