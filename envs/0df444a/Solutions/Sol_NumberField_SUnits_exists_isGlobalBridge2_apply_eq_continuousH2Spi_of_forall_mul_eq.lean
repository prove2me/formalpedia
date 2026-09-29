-- Prove2me | solution 1 for NumberField.SUnits.exists_isGlobalBridge2_apply_eq_continuousH2Spi_of_forall_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c0bd1f45-b5c4-56db-adb5-338f62f0a39a

import Mathlib
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_GlobalBridge
import Definitions.Def_GroupCohomology_RelationHomDefect
import Theorems.Thm_Rep_isZero_tateCohomology_ihom_free
import Theorems.Thm_Rep_homSeqOne_shortExact
import Theorems.Thm_NumberField_SUnits_isGlobalBridge2_apply_map_homSeq_f_eq_continuousH2Spi_of_eq_delta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_SUnits_exists_isGlobalBridge2_apply_eq_continuousH2Spi_of_forall_mul_eq
set_option autoImplicit false
p2m_open "CategoryTheory groupCohomology NumberField P2MW.S_NumberField_SUnits_exists_isGlobalBridge2_apply_eq_continuousH2Spi_of_forall_mul_eq.NumberField IsDedekindDomain ExtCitation"

namespace NumberField
p2m_export "NumberField" "place SUnits.sUnits SUnits.mem_sUnits_iff SUnits.sUnitsRep SUnits.val placesOverPrimes SUnits.isGlobalBridge2_apply_map_homSeq_f_eq_continuousH2Spi_of_eq_delta"
namespace SUnits
p2m_export "NumberField.SUnits" "sUnits mem_sUnits_iff sUnitsRep val isGlobalBridge2_apply_map_homSeq_f_eq_continuousH2Spi_of_eq_delta"
namespace HStabRealise
p2m_open "NumberField.SUnits NumberField"

section ihomEl

variable {G : Type} [Group G] (B E : Rep ℤ G)

attribute [local instance 10000] Rep.hV1 Rep.hV2

theorem ihom_ext {c c' : (ihom B).obj E}
    (h : ∀ b, LinearMap.toAddMonoidHom c b = LinearMap.toAddMonoidHom c' b) : c = c' :=
  LinearMap.ext h

theorem ihom_add_apply (c c' : (ihom B).obj E) (b : B) :
    LinearMap.toAddMonoidHom (c + c') b = LinearMap.toAddMonoidHom c b + LinearMap.toAddMonoidHom c' b := rfl

theorem ihom_rho_apply (g : G) (c : (ihom B).obj E) (b : B) :
    LinearMap.toAddMonoidHom (((ihom B).obj E).ρ g c) b = E.ρ g (LinearMap.toAddMonoidHom c (B.ρ g⁻¹ b)) := by
  erw [Rep.ihom_obj_ρ_apply]; rfl

noncomputable def mkIhom (f : B →+ E) : (ihom B).obj E where
  toFun := f
  map_add' := f.map_add
  map_smul' n b := by simpa using map_intCast_smul f ℤ ℤ n b

theorem mkIhom_apply (f : B →+ E) (b : B) : LinearMap.toAddMonoidHom (mkIhom B E f) b = f b := rfl

end ihomEl

section les

theorem exists_delta_eq {G : Type} [Group G] [Fintype G] (B E : Rep ℤ G) (h1 : (Rep.homSeq₁ B E).ShortExact)
    (y : groupCohomology ((ihom B).obj E) 2) :
    ∃ η : groupCohomology (Rep.defectQ B E) 1, (δ h1 1 2 rfl).hom η = y := by

  have hZ : Limits.IsZero (groupCohomology (Rep.homSeq₁ B E).X₂ 2) := Rep.isZero_tateCohomology_ihom_free B E 2
  have hex := groupCohomology.mapShortComplex₁_exact h1 (i := 1) (j := 2) rfl
  rw [ShortComplex.moduleCat_exact_iff] at hex
  have hg0 : ((mapShortComplex₁ h1 (rfl : 1 + 1 = 2)).g).hom y = 0 := by
    have h0 : (mapShortComplex₁ h1 (rfl : 1 + 1 = 2)).g = 0 := hZ.eq_of_tgt _ _
    rw [h0, ModuleCat.hom_zero, LinearMap.zero_apply]
  obtain ⟨η, hη⟩ := hex y hg0
  exact ⟨η, hη⟩

end les

section iota

variable {Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))} {F : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥F]
  (ιE : (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) →+ Additive (AlgebraicClosure ℚ)ˣ)
  (hιE : ∀ x, Additive.toMul (ιE x) =
    Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F Sℚ x))

include hιE

theorem iotaE_injective : Function.Injective ιE := by
  intro x y h
  have h' : ((Additive.toMul (ιE x) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = Additive.toMul (ιE y) := by rw [h]
  rw [hιE, hιE] at h'
  have h'' : NumberField.SUnits.val ℚ ↥F Sℚ x = NumberField.SUnits.val ℚ ↥F Sℚ y :=
    Units.ext ((algebraMap ↥F (AlgebraicClosure ℚ)).injective h')
  exact Subtype.ext (congrArg Additive.ofMul h'')

theorem iotaE_rho [IsGalois ℚ ↥F] (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) :
    ιE ((NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ).ρ (AlgEquiv.restrictNormalHom ↥F γ) x) =
      (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (ιE x) := by
  change _ = (Rep.ofMulDistribMulAction _ (AlgebraicClosure ℚ)ˣ).ρ γ (ιE x)
  rw [Rep.ofMulDistribMulAction_ρ_apply_apply]
  apply Additive.toMul.injective
  rw [toMul_ofMul, hιE, hιE]
  apply Units.ext
  change algebraMap ↥F (AlgebraicClosure ℚ) ((AlgEquiv.restrictNormalHom ↥F γ) (NumberField.SUnits.val ℚ ↥F Sℚ x : ↥F)) =
    γ (algebraMap ↥F (AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F Sℚ x : ↥F))
  exact AlgEquiv.restrictNormal_commutes γ ↥F _

omit hιE in

theorem valuation_eq_one_of_pow_eq_one {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {y : K}
    {n : ℕ} (hn : n ≠ 0) (hy : y ^ n = 1) : w.valuation K y = 1 := by
  have hv : (w.valuation K y) ^ n = 1 := by rw [← map_pow, hy, map_one]
  rcases lt_trichotomy (w.valuation K y) 1 with h | h | h
  · exact absurd hv (ne_of_lt (pow_lt_one₀ zero_le' h hn))
  · exact h
  · exact absurd hv (ne_of_gt (one_lt_pow₀ h hn))

variable {p : ℕ} [Fact p.Prime] {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) (hζF : ζ ∈ F)

include hζ hζF in

theorem exists_iotaE_eq_of_pow_eq_one (u : (AlgebraicClosure ℚ)ˣ) (hu : u ^ p = 1) :
    ∃ e : NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ, ιE e = Additive.ofMul u := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : NeZero p := ⟨hp0⟩
  have hzFp : (⟨ζ, hζF⟩ : ↥F) ^ p = 1 := by
    apply (algebraMap ↥F (AlgebraicClosure ℚ)).injective
    rw [map_pow, map_one]
    exact hζ.pow_eq_one
  set zU : (↥F)ˣ := Units.ofPowEqOne _ p hzFp hp0 with hzU
  have hzUp : zU ^ p = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hzFp)
  have hζU : IsPrimitiveRoot (Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ) zU) p :=
    IsPrimitiveRoot.coe_units_iff.1 hζ
  obtain ⟨i, -, hi⟩ := hζU.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity p u).mpr hu)
  have hmem : zU ^ i ∈ NumberField.SUnits.sUnits ℚ ↥F Sℚ := by
    rw [NumberField.SUnits.mem_sUnits_iff]
    intro σ w _
    apply valuation_eq_one_of_pow_eq_one w hp0
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, hzUp, one_pow, Units.val_one, map_one]
  refine ⟨⟨Additive.ofMul (zU ^ i), hmem⟩, ?_⟩
  apply Additive.toMul.injective
  rw [hιE, toMul_ofMul, ← hi, ← map_pow]
  rfl

omit [NumberField ↥F] hιE in

theorem mem_fixingSubgroup_of_restrictNormalHom_eq_one [IsGalois ℚ ↥F] (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hs : AlgEquiv.restrictNormalHom ↥F s = 1) : s ∈ F.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro a ha
  have h := AlgEquiv.restrictNormal_commutes s ↥F ⟨a, ha⟩
  rw [show s.restrictNormal ↥F = AlgEquiv.restrictNormalHom ↥F s from rfl, hs, AlgEquiv.one_apply] at h
  exact h.symm

end iota

section cocycle

local instance isAlgebraicQbar_hstab : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar_hstab : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance normalQbar_hstab : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

variable {p : ℕ} [Fact p.Prime] {Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))}
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F]
  (ιE : (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) →+ Additive (AlgebraicClosure ℚ)ˣ)
  (hιE : ∀ x, Additive.toMul (ιE x) =
    Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F Sℚ x))
  {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) (hζF : ζ ∈ F)
  {M : Rep.{0} (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
  {B : Rep.{0} ℤ (↥F ≃ₐ[ℚ] ↥F)} (hB : ∀ b : B, p • b = 0)
  (κ : B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)

omit [NumberField ↥F] in
include hB in

theorem toMul_kappa_pow (b : B) (x : M) : Additive.toMul (κ b x) ^ p = 1 := by
  have h := map_nsmul (κ.flip x) p b
  rw [hB b, map_zero] at h
  have h2 := congrArg Additive.toMul h
  rw [toMul_zero, toMul_nsmul] at h2
  exact h2.symm

include hιE hζ hζF hB in
theorem exists_read (x : M) (b : B) : ∃ e : (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ), ιE e = κ b x :=
  exists_iotaE_eq_of_pow_eq_one ιE hιE hζ hζF (Additive.toMul (κ b x)) (toMul_kappa_pow F hB κ b x)

noncomputable def readFun (x : M) (b : B) : (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) :=
  @dite _ (∃ e : (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ), ιE e = κ b x) (Classical.dec _) (fun h => h.choose) (fun _ => 0)

include hιE hζ hζF hB in
theorem iotaE_readFun (x : M) (b : B) : ιE (readFun F ιE κ x b) = κ b x := by
  have h := exists_read F ιE hιE hζ hζF hB κ x b
  show ιE (@dite _ (∃ e : (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ), ιE e = κ b x) (Classical.dec _) (fun h => h.choose) (fun _ => 0)) = _
  rw [dif_pos h]
  exact h.choose_spec

noncomputable def readAdd (x : M) : B →+ (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) where
  toFun := readFun F ιE κ x
  map_zero' := iotaE_injective ιE hιE (by rw [iotaE_readFun F ιE hιE hζ hζF hB κ, map_zero, map_zero, AddMonoidHom.zero_apply])
  map_add' b b' := iotaE_injective ιE hιE (by
    rw [map_add, iotaE_readFun F ιE hιE hζ hζF hB κ, iotaE_readFun F ιE hιE hζ hζF hB κ,
      iotaE_readFun F ιE hιE hζ hζF hB κ, map_add, AddMonoidHom.add_apply])

noncomputable def readM (x : M) : (ihom B).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) := mkIhom B (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) (readAdd F ιE hιE hζ hζF hB κ x)

theorem iotaE_readM_apply (x : M) (b : B) :
    ιE (LinearMap.toAddMonoidHom (readM F ιE hιE hζ hζF hB κ x) b) = κ b x :=
  iotaE_readFun F ιE hιE hζ hζF hB κ x b

theorem readM_add (x y : M) :
    readM F ιE hιE hζ hζF hB κ (x + y) = readM F ιE hιE hζ hζF hB κ x + readM F ιE hιE hζ hζF hB κ y := by
  apply ihom_ext; intro b; apply iotaE_injective ιE hιE
  rw [ihom_add_apply, map_add, iotaE_readM_apply, iotaE_readM_apply, iotaE_readM_apply, map_add]

variable [IsGalois ℚ ↥F]
  (hκeq : ∀ (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (b : B) (x : M),
    κ (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) (M.ρ γ x) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (κ b x))

include hκeq in

theorem rho_readM (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : M) :
    ((ihom B).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)).ρ (AlgEquiv.restrictNormalHom ↥F γ) (readM F ιE hιE hζ hζF hB κ x) = readM F ιE hιE hζ hζF hB κ (M.ρ γ x) := by
  apply ihom_ext; intro b; apply iotaE_injective ιE hιE
  rw [ihom_rho_apply, iotaE_rho ιE hιE, iotaE_readM_apply, iotaE_readM_apply]
  have hb : B.ρ (AlgEquiv.restrictNormalHom ↥F γ) (B.ρ (AlgEquiv.restrictNormalHom ↥F γ)⁻¹ b) = b := by
    show (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) * B.ρ (AlgEquiv.restrictNormalHom ↥F γ)⁻¹) b = b
    rw [← map_mul, mul_inv_cancel, map_one]; rfl
  rw [← hκeq γ (B.ρ (AlgEquiv.restrictNormalHom ↥F γ)⁻¹ b) x, hb]

omit [NumberField ↥F] in
theorem restrictNormalHom_surjective' :
    Function.Surjective (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) ↥F) := AlgEquiv.restrictNormalHom_surjective _

noncomputable def sec : (↥F ≃ₐ[ℚ] ↥F) → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  Function.surjInv (restrictNormalHom_surjective' F)

omit [NumberField ↥F] in
theorem pi_sec (g : ↥F ≃ₐ[ℚ] ↥F) : AlgEquiv.restrictNormalHom ↥F (sec F g) = g := Function.surjInv_eq _ g

omit [NumberField ↥F] in
theorem inv_mul_sec_mem (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : γ⁻¹ * sec F (AlgEquiv.restrictNormalHom ↥F γ) ∈ F.fixingSubgroup :=
  mem_fixingSubgroup_of_restrictNormalHom_eq_one _ (by rw [map_mul, map_inv, pi_sec, inv_mul_cancel])

variable (m : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M)
  (hmF : ∀ (g g' s s' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), s ∈ F.fixingSubgroup → s' ∈ F.fixingSubgroup →
    m (g * s, g' * s') = m (g, g'))

noncomputable def cFun : (↥F ≃ₐ[ℚ] ↥F) × (↥F ≃ₐ[ℚ] ↥F) → (ihom B).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) :=
  fun q => readM F ιE hιE hζ hζF hB κ (m (sec F q.1, sec F q.2))

include hmF in

theorem cFun_apply (γ₁ γ₂ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    cFun F ιE hιE hζ hζF hB κ m (AlgEquiv.restrictNormalHom ↥F γ₁, AlgEquiv.restrictNormalHom ↥F γ₂) = readM F ιE hιE hζ hζF hB κ (m (γ₁, γ₂)) := by
  show readM F ιE hιE hζ hζF hB κ (m (sec F (AlgEquiv.restrictNormalHom ↥F γ₁), sec F (AlgEquiv.restrictNormalHom ↥F γ₂))) = _
  have key : m (sec F (AlgEquiv.restrictNormalHom ↥F γ₁), sec F (AlgEquiv.restrictNormalHom ↥F γ₂)) = m (γ₁, γ₂) := by
    have h := hmF γ₁ γ₂ _ _ (inv_mul_sec_mem F γ₁) (inv_mul_sec_mem F γ₂)
    rwa [mul_inv_cancel_left, mul_inv_cancel_left] at h
  rw [key]

include hmF hκeq in

theorem cFun_mem (hm2 : m ∈ cocycles₂ M) : cFun F ιE hιE hζ hζF hB κ m ∈ cocycles₂ ((ihom B).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)) := by
  rw [mem_cocycles₂_iff]
  intro g h j
  obtain ⟨γg, rfl⟩ := restrictNormalHom_surjective' F g
  obtain ⟨γh, rfl⟩ := restrictNormalHom_surjective' F h
  obtain ⟨γj, rfl⟩ := restrictNormalHom_surjective' F j
  have e1 := cFun_apply F ιE hιE hζ hζF hB κ m hmF (γg * γh) γj
  have e2 := cFun_apply F ιE hιE hζ hζF hB κ m hmF γg γh
  have e3 := cFun_apply F ιE hιE hζ hζF hB κ m hmF γh γj
  have e4 := cFun_apply F ιE hιE hζ hζF hB κ m hmF γg (γh * γj)
  rw [map_mul] at e1 e4
  simp only [e1, e2, e3, e4]
  rw [rho_readM F ιE hιE hζ hζF hB κ hκeq, ← readM_add, ← readM_add]
  exact congrArg (readM F ιE hιE hζ hζF hB κ) ((mem_cocycles₂_iff m).1 hm2 γg γh γj)

noncomputable def cocycle (hm2 : m ∈ cocycles₂ M) : cocycles₂ ((ihom B).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)) :=
  ⟨cFun F ιE hιE hζ hζF hB κ m, cFun_mem F ιE hιE hζ hζF hB κ hκeq m hmF hm2⟩

include hmF in

theorem kappa_m_eq (hm2 : m ∈ cocycles₂ M) (γ₁ γ₂ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B) :
    κ b (m (γ₁, γ₂)) = ιE (LinearMap.toAddMonoidHom
      ((cocycle F ιE hιE hζ hζF hB κ hκeq m hmF hm2 : (↥F ≃ₐ[ℚ] ↥F) × (↥F ≃ₐ[ℚ] ↥F) → (ihom B).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ))
        (AlgEquiv.restrictNormalHom ↥F γ₁, AlgEquiv.restrictNormalHom ↥F γ₂)) b) := by
  show _ = ιE (LinearMap.toAddMonoidHom (cFun F ιE hιE hζ hζF hB κ m (AlgEquiv.restrictNormalHom ↥F γ₁, AlgEquiv.restrictNormalHom ↥F γ₂)) b)
  rw [cFun_apply F ιE hιE hζ hζF hB κ m hmF, iotaE_readM_apply]

end cocycle

end NumberField.SUnits.HStabRealise

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] (hF : F.IsUnramifiedOutside S)
    (hζF : ζ ∈ F) (hFM : ∀ s ∈ F.fixingSubgroup, ∀ x : M, M.ρ s x = x)
    (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) [Fintype B] (hB : ∀ b : B, p • b = 0)
    (ιE : (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE : ∀ x, Additive.toMul (ιE x) = Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F Sℚ x))
    (κ : B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hκeq : ∀ (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (b : B) (x : M),
      κ (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) (M.ρ γ x) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (κ b x))
    (hκ : ∀ c : B →+ Additive (AlgebraicClosure ℚ)ˣ, ∃! x : M, ∀ b, κ b x = c b)
    {ΛE : H1 ((ihom (Rep.relationModuleInt B)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)) →+ continuousH2S S M}
    (hΛE : IsGlobalBridge₂ S (AlgEquiv.restrictNormalHom ↥F) (Rep.relationModuleInt.ι B) (Rep.freeCover B)
      (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) ιE κ ΛE)

    (m : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M)
    (hm : m ∈ levelCocyclesS₂ S M)
    (hmF : ∀ (g g' s s' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), s ∈ F.fixingSubgroup → s' ∈ F.fixingSubgroup →
      m (g * s, g' * s') = m (g, g')) :
    ∃ x, ΛE x = continuousH2Sπ S M ⟨m, hm⟩ := by
  have _ := hFM
  have h1 := Rep.homSeqOne_shortExact B (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)
  have hm2 : m ∈ cocycles₂ M := ((mem_levelCocyclesS₂_iff S M m).1 hm).1
  haveI instFintypeGalF : Fintype (↥F ≃ₐ[ℚ] ↥F) := Fintype.ofFinite _
  obtain ⟨η, hη⟩ := NumberField.SUnits.HStabRealise.exists_delta_eq B (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) h1
    ((H2π _).hom (NumberField.SUnits.HStabRealise.cocycle F ιE hιE hζ hζF hB κ hκeq m hmF hm2))
  exact ⟨_, NumberField.SUnits.isGlobalBridge2_apply_map_homSeq_f_eq_continuousH2Spi_of_eq_delta S hpS Sℚ hSℚ M F hF B hB
    h1 ιE hιE κ hκeq hκ hΛE η (NumberField.SUnits.HStabRealise.cocycle F ιE hιE hζ hζF hB κ hκeq m hmF hm2) hη.symm m
    (NumberField.SUnits.HStabRealise.kappa_m_eq F ιE hιE hζ hζF hB κ hκeq m hmF hm2) hm⟩

end S_NumberField_SUnits_exists_isGlobalBridge2_apply_eq_continuousH2Spi_of_forall_mul_eq
end P2MW
export P2MW.S_NumberField_SUnits_exists_isGlobalBridge2_apply_eq_continuousH2Spi_of_forall_mul_eq (solution)
