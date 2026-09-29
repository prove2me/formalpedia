-- Prove2me | solution 1 for NumberField.finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/094b24b3-3bac-5992-8518-9c04556132f7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 6400000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

section

namespace ContinuousAlgHom p2m_export "ContinuousAlgHom" "mk ext" end ContinuousAlgHom
p2m_open_scoped "ContinuousAlgHom" in
nonrec
scoped instance ContinuousAlgHom.isLocalHom_id {R A : Type*}
    [CommSemiring R] [Semiring A] [Algebra R A] [TopologicalSpace A] :
    IsLocalHom (ContinuousAlgHom.id R A) := by
  convert isLocalHom_id A
  exact ⟨fun ⟨H⟩ ↦ ⟨H⟩, fun ⟨H⟩ ↦ ⟨H⟩⟩

p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom"
namespace AlgebraicClosure p2m_export "AlgebraicClosure" "isAlgebraic" end AlgebraicClosure
namespace AlgebraicClosure
p2m_open_scoped "AlgebraicClosure" in
private noncomputable
def _root_.AlgebraicClosure.map {K L : Type*} [Field K] [Field L] (f : K →+* L) :
    AlgebraicClosure K →+* AlgebraicClosure L :=
  letI := f.toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L).toRingHom

end AlgebraicClosure
p2m_export "" "AlgebraicClosure.map"
namespace IsModuleTopology p2m_export "IsModuleTopology" "continuous_of_linearMap toContinuousAdd mk instPi" end IsModuleTopology
p2m_open_scoped "IsModuleTopology" in
nonrec
lemma IsModuleTopology.continuous_det {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {M : Type*} [AddCommGroup M] [Module A M]
    [TopologicalSpace (Module.End A M)] [IsModuleTopology A (Module.End A M)] :
    Continuous (LinearMap.det : Module.End A M →* A) := by
  classical
  by_cases H : ∃ s : Finset M, Nonempty (Module.Basis s A M)
  · obtain ⟨s, ⟨b⟩⟩ := H
    have : IsModuleTopology A (Matrix s s A) := IsModuleTopology.instPi
    have : ContinuousAdd (Module.End A M) := IsModuleTopology.toContinuousAdd A _
    letI e : Module.End A M ≃A[A] Matrix s s A :=
    { __ := algEquivMatrix b,
      continuous_toFun := continuous_of_linearMap (algEquivMatrix b).toLinearMap,
      continuous_invFun := continuous_of_linearMap (algEquivMatrix b).symm.toLinearMap }
    rw [e.symm.isQuotientMap.continuous_iff]
    convert continuous_id.matrix_det (R := A) (n := s)
    first
      | (ext M; exact LinearMap.det_toLin b M)
      | exact LinearMap.det_toLin b _
  rw [LinearMap.det, dif_neg H]
  exact continuous_of_const fun x ↦ congrFun rfl

scoped instance {K L : Type*} [Field K] [Field L] [Algebra K L] [NumberField K]
    (E : IntermediateField K L) [FiniteDimensional K E] : NumberField E where
  to_finiteDimensional := .trans ℚ K E

namespace Additive p2m_export "Additive" "ext toMul sub add ofMul" end Additive
p2m_open_scoped "Additive" in
noncomputable
scoped instance Additive.instDistrbMulAction
    {G M : Type*} [Monoid G] [Monoid M] [MulDistribMulAction G M] :
    DistribMulAction G (Additive M) where
  smul g m := .ofMul (g • m.toMul)
  one_smul m := one_smul _ m.toMul
  mul_smul g h m := mul_smul g h m.toMul
  smul_zero g := smul_one (N := M) g
  smul_add g m n := MulDistribMulAction.smul_mul g m.toMul n.toMul

p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive"
end
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive"

section

universe v

p2m_open "WeierstrassCurve P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.WeierstrassCurve"

local instance isAlgebraicQbar_complexConjugation : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar_complexConjugation : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance normalQbar_complexConjugation : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

noncomputable def complexEmbedding : AlgebraicClosure ℚ →ₐ[ℚ] ℂ :=
  IsAlgClosed.lift

lemma complexEmbedding_injective : Function.Injective complexEmbedding :=
  complexEmbedding.injective

noncomputable local instance instAlgebraQbarComplex : Algebra (AlgebraicClosure ℚ) ℂ :=
  complexEmbedding.toRingHom.toAlgebra

local instance instTowerQbarComplex : IsScalarTower ℚ (AlgebraicClosure ℚ) ℂ :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

noncomputable def complexConjAlgEquiv : ℂ ≃ₐ[ℚ] ℂ :=
  AlgEquiv.ofRingEquiv (f := starRingAut) fun x => map_ratCast (starRingEnd ℂ) x

lemma complexConjAlgEquiv_mul_self : complexConjAlgEquiv * complexConjAlgEquiv = 1 :=
  AlgEquiv.ext fun z => Complex.conj_conj z

noncomputable def complexConjugation : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ :=
  AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ℂ) (AlgebraicClosure ℚ) complexConjAlgEquiv

theorem complexEmbedding_complexConjugation (x : AlgebraicClosure ℚ) :
    complexEmbedding (complexConjugation x) = starRingEnd ℂ (complexEmbedding x) :=
  AlgEquiv.restrictNormal_commutes complexConjAlgEquiv (AlgebraicClosure ℚ) x

theorem complexConjugation_mul_self : complexConjugation * complexConjugation = 1 := by
  rw [complexConjugation, ← map_mul, complexConjAlgEquiv_mul_self, map_one]

lemma map_complexEmbedding_mem_rootsOfUnity {n : ℕ} {t : (AlgebraicClosure ℚ)ˣ}
    (ht : t ∈ rootsOfUnity n (AlgebraicClosure ℚ)) :
    Units.map (complexEmbedding : AlgebraicClosure ℚ →* ℂ) t ∈ rootsOfUnity n ℂ := by
  rw [mem_rootsOfUnity] at ht ⊢
  rw [← map_pow, ht, map_one]

theorem complexConjugation_rootsOfUnity {n : ℕ} [NeZero n] {t : (AlgebraicClosure ℚ)ˣ}
    (ht : t ∈ rootsOfUnity n (AlgebraicClosure ℚ)) :
    complexConjugation (t : AlgebraicClosure ℚ) = ((t⁻¹ : (AlgebraicClosure ℚ)ˣ) :
      AlgebraicClosure ℚ) := by
  apply complexEmbedding_injective
  rw [complexEmbedding_complexConjugation]
  have h1 : complexEmbedding (t : AlgebraicClosure ℚ) =
      ((Units.map (complexEmbedding : AlgebraicClosure ℚ →* ℂ) t : ℂˣ) : ℂ) := rfl
  have h2 : complexEmbedding ((t⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      (((Units.map (complexEmbedding : AlgebraicClosure ℚ →* ℂ) t)⁻¹ : ℂˣ) : ℂ) := by
    rw [← map_inv]; rfl
  rw [h1, h2]
  exact Complex.conj_rootsOfUnity (map_complexEmbedding_mem_rootsOfUnity ht)

lemma rootsOfUnity_inv_eq_pow {M : Type*} [CommMonoid M] {n : ℕ} [NeZero n] {t : Mˣ}
    (ht : t ∈ rootsOfUnity n M) : t⁻¹ = t ^ (n - 1) := by
  rw [mem_rootsOfUnity] at ht
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel (NeZero.one_le), ht]

namespace ZMod p2m_export "ZMod" "nontrivial_iff lift card val val_neg_one val_one repr smul_mem map_smul" end ZMod
p2m_open_scoped "ZMod" in
lemma ZMod.val_neg_one' (n : ℕ) [NeZero n] : (-1 : ZMod n).val = n - 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact (ZMod.val_neg_one m).trans (Nat.succ_sub_one m).symm

theorem modularCyclotomicCharacter_complexConjugation (n : ℕ) [NeZero n]
    (hn : Nat.card (rootsOfUnity n (AlgebraicClosure ℚ)) = n) :
    modularCyclotomicCharacter (AlgebraicClosure ℚ) hn
      (complexConjugation : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) = -1 := by
  have key : (-1 : ZMod n) = (modularCyclotomicCharacter (AlgebraicClosure ℚ) hn
      (complexConjugation : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) : ZMod n) := by
    refine modularCyclotomicCharacter.unique _ _ _ fun t ht => ?_
    show complexConjugation (t : AlgebraicClosure ℚ) = _
    rw [complexConjugation_rootsOfUnity ht, rootsOfUnity_inv_eq_pow ht, ZMod.val_neg_one' n]
    exact Units.val_pow_eq_pow_val t (n - 1)
  refine Units.ext ?_
  rw [Units.val_neg, Units.val_one]
  exact key.symm

namespace FreyPackage

p2m_open "WeierstrassCurve.Affine.Point P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.WeierstrassCurve.Affine.Point"
p2m_open_scoped "WeierstrassCurve.Affine P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.WeierstrassCurve.Affine"

end FreyPackage
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive"

end
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive"

section

universe r s v

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map mk isIntegral_iff IsIntegral Affine.Point j"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "map Point"
namespace Point
p2m_export "WeierstrassCurve.Affine.Point" "add map_zero map mk"
p2m_open "WeierstrassCurve.Affine.Point WeierstrassCurve.Affine WeierstrassCurve"

p2m_open "WeierstrassCurve P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.WeierstrassCurve"

variable {R : Type r} {S : Type s} {K : Type v} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] {W' : Affine R} [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K]

end WeierstrassCurve.Affine.Point
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive"
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive"
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive"

section AlgClosed

namespace IsAlgClosed p2m_export "IsAlgClosed" "lift mk" end IsAlgClosed
p2m_open_scoped "IsAlgClosed" in
theorem IsAlgClosed.card_rootsOfUnity_eq (K : Type v) [Field K] [IsAlgClosed K] [CharZero K]
    (n : ℕ) [NeZero n] : Nat.card (rootsOfUnity n K) = n :=
  haveI : NeZero (n : K) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
  HasEnoughRootsOfUnity.natCard_rootsOfUnity K n

end AlgClosed
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive"

namespace FreyPackage

p2m_open "WeierstrassCurve.Affine.Point P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.WeierstrassCurve.Affine.Point"

end FreyPackage
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive"

end
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive"

section

p2m_open "IntermediateField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

namespace IntermediateField
p2m_export "IntermediateField" "toAlgebra eq_of_le_of_finrank_le mk val lift_le finrank_fixedField_eq_card mem_lift isIntegral_iff mem_fixedField_iff lift inclusion ext adjoin_simple_le_iff algebraMap_apply smul_def fixedField adjoin.finrank liftAlgEquiv adjoin fixingSubgroup_fixedField lift_inj comap mem_top mem_bot smul_mem normal map"
p2m_open "IntermediateField"

scoped instance (priority := 1010) ratAlgebra {L : Type*} [Field L] [Algebra ℚ L]
    (E : IntermediateField ℚ L) : Algebra ℚ E :=
  DivisionRing.toRatAlgebra

end IntermediateField
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

namespace AlgHom
p2m_export "AlgHom" "ext toLinearMap mk toRingHom End mk' card Finite mem_range restrictNormal_commutes"
p2m_open "AlgHom"

end AlgHom
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

namespace ModularCurve

variable (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

end ModularCurve
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

end
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

section

p2m_open "Module NumberField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.NumberField IntermediateField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"
p2m_open "WeierstrassCurve P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.WeierstrassCurve WeierstrassCurve.Affine.Point P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.WeierstrassCurve.Affine.Point"
p2m_open_scoped "WeierstrassCurve.Affine P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.WeierstrassCurve.Affine"

noncomputable section

namespace FLT
namespace ModThreeTwoGroupCommutativity

section GroupTheory

variable {H : Type*} [Group H] [Finite H]

theorem normal_of_isCoatom_of_isPGroup (hp : IsPGroup 2 H) {M : Subgroup H}
    (hM : IsCoatom M) : M.Normal :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent H := hp.isNilpotent
  Subgroup.NormalizerCondition.normal_of_coatom M
    Group.normalizerCondition_of_isNilpotent hM

theorem index_eq_two_of_isCoatom_of_isPGroup (hp : IsPGroup 2 H) {M : Subgroup H}
    (hM : IsCoatom M) : M.index = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : M.Normal := normal_of_isCoatom_of_isPGroup hp hM

  obtain ⟨n, hn⟩ := hp.index M
  rcases n with - | m
  · exact absurd (Subgroup.index_eq_one.mp (by simpa using hn)) hM.1
  rcases m with - | k
  · simpa using hn

  exfalso

  have hcard : Nat.card (H ⧸ M) = 2 ^ (k + 2) := hn
  haveI : Nontrivial (H ⧸ M) := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    rw [hcard]
    calc (1 : ℕ) < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

  obtain ⟨g, hg⟩ : ∃ g : H ⧸ M, orderOf g = 2 :=
    exists_prime_orderOf_dvd_card' 2 (by rw [hcard]; exact dvd_pow_self 2 (by omega))

  have hgbot : Subgroup.zpowers g ≠ ⊥ := by
    intro hbot
    have : g = 1 := by
      have := Subgroup.mem_zpowers g
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    rw [this, orderOf_one] at hg
    omega
  have hgtop : Subgroup.zpowers g ≠ ⊤ := by
    intro htop
    have hcards : Nat.card (Subgroup.zpowers g) = Nat.card (⊤ : Subgroup (H ⧸ M)) := by
      rw [htop]
    rw [Nat.card_zpowers g, hg, Subgroup.card_top, hcard] at hcards
    have : (4 : ℕ) ≤ 2 ^ (k + 2) := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

  have hsurj : Function.Surjective (QuotientGroup.mk' M) := QuotientGroup.mk'_surjective M
  have hlt₁ : M < (Subgroup.zpowers g).comap (QuotientGroup.mk' M) := by
    have hle : M ≤ (Subgroup.zpowers g).comap (QuotientGroup.mk' M) :=
      le_trans (le_of_eq (QuotientGroup.ker_mk' M).symm)
        (Subgroup.ker_le_comap (QuotientGroup.mk' M) (Subgroup.zpowers g))
    refine lt_of_le_of_ne hle fun heq => hgbot ?_
    refine (Subgroup.comap_injective hsurj ?_).symm
    rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
    exact heq
  have hlt₂ : (Subgroup.zpowers g).comap (QuotientGroup.mk' M) < ⊤ := by
    refine Ne.lt_top fun htop => hgtop ?_
    exact Subgroup.comap_injective hsurj (htop.trans (Subgroup.comap_top _).symm)
  exact absurd (hM.2 _ hlt₁) hlt₂.ne

theorem exists_zpowers_eq_top_of_subsingleton_coatom [Nontrivial H]
    (huniq : ∀ M₁ M₂ : Subgroup H, IsCoatom M₁ → IsCoatom M₂ → M₁ = M₂) :
    ∃ x : H, Subgroup.zpowers x = ⊤ := by

  obtain ⟨M₀, hM₀⟩ : ∃ M : Subgroup H, IsCoatom M := by
    rcases IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup H) with hbot | ⟨M, hM, -⟩
    · obtain ⟨x, hx⟩ := exists_ne (1 : H)
      have hxbot : x ∈ (⊥ : Subgroup H) := by rw [hbot]; exact Subgroup.mem_top x
      exact absurd (Subgroup.mem_bot.mp hxbot) hx
    · exact ⟨M, hM⟩

  obtain ⟨x, hx⟩ : ∃ x : H, x ∉ M₀ := by
    by_contra hall
    push Not at hall
    exact hM₀.1 ((Subgroup.eq_top_iff' M₀).mpr hall)
  refine ⟨x, ?_⟩

  rcases IsCoatomic.eq_top_or_exists_le_coatom (Subgroup.zpowers x) with htop | ⟨M, hM, hle⟩
  · exact htop
  · exact absurd (hle (Subgroup.mem_zpowers x)) (huniq M M₀ hM hM₀ ▸ hx)

end GroupTheory
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

end FLT.ModThreeTwoGroupCommutativity
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

namespace FreyPackage

open FLT.ModThreeTwoGroupCommutativity

end FreyPackage
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

namespace FLT
namespace ModThreeTwoGroupCommutativity

end FLT.ModThreeTwoGroupCommutativity
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

end
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

end
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

section

open Module

attribute [local instance] FractionRing.liftAlgebra

namespace Ideal
p2m_export "Ideal" "Quotient.eq_zero_iff_mem ker_le_comap mul_mem_right pow_le_pow_right isUnit_iff mem_bot span mem_of_liesOver IsMaximal exists_maximal_ideal_liesOver_of_isIntegral Quotient.mk dvd_iff_le mul_mem_left map exists_le_maximal IsMaximal.ne_top ext absNorm absNorm_apply finiteQuotientOfFreeOfNeBot comap_top comap Quotient.nontrivial_iff eq_top_iff_one subset_span Quotient.mk_surjective absNorm_dvd_absNorm_of_le"
p2m_open "Ideal"

variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Module.Free ℤ S] [Module.Finite ℤ S]

theorem exists_isMaximal_le_natCast_mem_of_prime_dvd_absNorm {I : Ideal S} (hI : I ≠ ⊥)
    {q : ℕ} (hq : q.Prime) (hdvd : q ∣ I.absNorm) :
    ∃ P : Ideal S, P.IsMaximal ∧ I ≤ P ∧ (q : S) ∈ P := by
  haveI : Fact q.Prime := ⟨hq⟩

  haveI hfin : Finite (S ⧸ I) := I.finiteQuotientOfFreeOfNeBot hI
  have hcard : Nat.card (S ⧸ I) = I.absNorm := (I.absNorm_apply).symm

  obtain ⟨y, hy⟩ := exists_prime_addOrderOf_dvd_card' (G := S ⧸ I) q (by rw [hcard]; exact hdvd)

  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hqx : (q : S) * x ∈ I := by
    have h0 : (q : ℕ) • (Ideal.Quotient.mk I x) = 0 := by
      rw [← hy]; exact addOrderOf_nsmul_eq_zero _
    rw [← map_nsmul] at h0
    have := Ideal.Quotient.eq_zero_iff_mem.mp h0
    rwa [nsmul_eq_mul] at this
  have hx : x ∉ I := by
    intro hmem
    have h0 : Ideal.Quotient.mk I x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [h0, addOrderOf_zero] at hy
    exact hq.one_lt.ne' hy.symm

  have hqcolon : (q : S) ∈ I.colon {x} := by
    rw [Submodule.mem_colon_singleton, smul_eq_mul]; exact hqx
  have hIcolon : I ≤ I.colon {x} := fun r hr => by
    rw [Submodule.mem_colon_singleton, smul_eq_mul]; exact I.mul_mem_right x hr
  have hcolon_ne_top : I.colon {x} ≠ ⊤ := by
    intro htop
    have h1 : (1 : S) ∈ I.colon {x} := htop ▸ Submodule.mem_top
    rw [Submodule.mem_colon_singleton, one_smul] at h1
    exact hx h1
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hcolon_ne_top
  exact ⟨P, hPmax, hIcolon.trans hle, hle hqcolon⟩

omit [Module.Finite ℤ S] in

theorem prime_dvd_absNorm_of_natCast_mem {P : Ideal S} (hP : P ≠ ⊤)
    {q : ℕ} (hq : q.Prime) (hqP : (q : S) ∈ P) :
    q ∣ P.absNorm := by

  have hq1 : (q : ℕ) • (1 : S ⧸ P) = 0 := by
    rw [nsmul_eq_mul, mul_one, ← map_natCast (Ideal.Quotient.mk P)]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hqP
  have hone : (1 : S ⧸ P) ≠ 0 := by
    haveI : Nontrivial (S ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hP
    exact one_ne_zero
  have horder : addOrderOf (1 : S ⧸ P) = q := by
    have hdvd : addOrderOf (1 : S ⧸ P) ∣ q := addOrderOf_dvd_of_nsmul_eq_zero hq1
    rcases (Nat.dvd_prime hq).mp hdvd with h1 | h
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) hone
    · exact h
  calc q = addOrderOf (1 : S ⧸ P) := horder.symm
    _ ∣ Nat.card (S ⧸ P) := addOrderOf_dvd_natCard _
    _ = P.absNorm := P.absNorm_apply.symm

end Ideal
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

namespace NumberField
p2m_export "NumberField" "abs_discr_gt_two integralBasis_apply discr mk integralBasis to_finiteDimensional RingOfIntegers RingOfIntegers.basis absNorm_differentIdeal discr_ne_zero to_charZero RingOfIntegers.algebraMap.injective integralBasis_repr_apply coe_discr"
p2m_open "NumberField"

p2m_open_scoped "NumberField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.NumberField"

variable (F : Type*) [Field F] [NumberField F] [Normal ℚ F]

theorem exists_isMaximal_dvd_differentIdeal_of_prime_dvd_discr (K : Type*) [Field K]
    [NumberField K] {q : ℕ} (hq : q.Prime) (hdvd : q ∣ (discr K).natAbs) :
    ∃ P : Ideal (𝓞 K), P.IsMaximal ∧ (q : 𝓞 K) ∈ P ∧ P ∣ differentIdeal ℤ (𝓞 K) := by

  have hnorm : (differentIdeal ℤ (𝓞 K)).absNorm = (discr K).natAbs :=
    absNorm_differentIdeal (K := K) (𝒪 := 𝓞 K)
  have hbot : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot

  obtain ⟨P, hPmax, hle, hqP⟩ :=
    Ideal.exists_isMaximal_le_natCast_mem_of_prime_dvd_absNorm hbot hq (hnorm ▸ hdvd)
  exact ⟨P, hPmax, hqP, Ideal.dvd_iff_le.mpr hle⟩

theorem prime_dvd_discr_of_dvd_differentIdeal (K : Type*) [Field K] [NumberField K]
    {q : ℕ} (hq : q.Prime) {P : Ideal (𝓞 K)} (hPmax : P.IsMaximal) (hqP : (q : 𝓞 K) ∈ P)
    (hram : P ∣ differentIdeal ℤ (𝓞 K)) :
    q ∣ (discr K).natAbs := by

  have hnorm : (differentIdeal ℤ (𝓞 K)).absNorm = (discr K).natAbs :=
    absNorm_differentIdeal (K := K) (𝒪 := 𝓞 K)
  calc q ∣ P.absNorm := Ideal.prime_dvd_absNorm_of_natCast_mem hPmax.ne_top hq hqP
    _ ∣ (differentIdeal ℤ (𝓞 K)).absNorm :=
        Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hram)
    _ = (discr K).natAbs := hnorm

theorem forall_isUnramifiedAt_iff_not_dvd_discr (K : Type*) [Field K] [NumberField K]
    {q : ℕ} (hq : q.Prime) :
    (∀ (P : Ideal (𝓞 K)) [P.IsMaximal], (q : 𝓞 K) ∈ P → Algebra.IsUnramifiedAt ℤ P) ↔
      ¬ q ∣ (discr K).natAbs := by
  haveI : Algebra.IsAlgebraic (FractionRing ℤ) (FractionRing (𝓞 K)) :=
    isAlgebraic_of_isFractionRing (R := ℤ) (S := 𝓞 K) (FractionRing ℤ) (FractionRing (𝓞 K))
  haveI : Algebra.IsIntegral (FractionRing ℤ) (FractionRing (𝓞 K)) :=
    Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  constructor
  · intro H hdvd
    obtain ⟨P, hPmax, hqP, hram⟩ :=
      exists_isMaximal_dvd_differentIdeal_of_prime_dvd_discr K hq hdvd
    haveI := hPmax
    exact dvd_differentIdeal_iff.mp hram (H P hqP)
  · intro H P hPmax hqP
    by_contra hram
    exact H (prime_dvd_discr_of_dvd_differentIdeal K hq hPmax hqP
      (dvd_differentIdeal_iff.mpr hram))

theorem prime_mem_of_dvd_discr_of_forall_isUnramifiedAt (K : Type*) [Field K] [NumberField K]
    (S : Set ℕ)
    (H : ∀ q : ℕ, q.Prime → q ∉ S →
      ∀ (P : Ideal (𝓞 K)) [P.IsMaximal], (q : 𝓞 K) ∈ P → Algebra.IsUnramifiedAt ℤ P)
    {q : ℕ} (hq : q.Prime) (hdvd : q ∣ (discr K).natAbs) : q ∈ S := by
  by_contra hqS
  exact (forall_isUnramifiedAt_iff_not_dvd_discr K hq).mp (H q hq hqS) hdvd

end NumberField
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

end
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

section

open Module

namespace FLT
namespace Gapsw7X2cTwoGroupCyclicReduction

open FLT.ModThreeTwoGroupCommutativity

theorem gapsw7_x2c_two_index_two_or_generated {G : Type*} [Group G] [Finite G]
    [Nontrivial G] (hcard : Nat.card G ∣ 16) :
    (∃ M₁ M₂ : Subgroup G, M₁ ≠ M₂ ∧ M₁.index = 2 ∧ M₂.index = 2) ∨
      ∃ x : G, ∀ g : G, g ∈ Subgroup.zpowers x := by
  obtain ⟨k, -, hk⟩ : ∃ k, k ≤ 4 ∧ Nat.card G = 2 ^ k := by
    have h16 : Nat.card G ∣ 2 ^ 4 := by
      have h4 : (2 : ℕ) ^ 4 = 16 := by norm_num
      rw [h4]
      exact hcard
    exact (Nat.dvd_prime_pow Nat.prime_two).mp h16
  have hp : IsPGroup 2 G := IsPGroup.of_card hk
  by_cases huniq : ∀ M₁ M₂ : Subgroup G, IsCoatom M₁ → IsCoatom M₂ → M₁ = M₂
  · obtain ⟨x, hx⟩ := exists_zpowers_eq_top_of_subsingleton_coatom huniq
    refine Or.inr ⟨x, fun g => ?_⟩
    rw [hx]
    exact Subgroup.mem_top g
  · push Not at huniq
    obtain ⟨M₁, M₂, h₁, h₂, hne⟩ := huniq
    exact Or.inl ⟨M₁, M₂, hne, index_eq_two_of_isCoatom_of_isPGroup hp h₁,
      index_eq_two_of_isCoatom_of_isPGroup hp h₂⟩

theorem gapsw7_x2c_sq_one_mem_of_index_two {G : Type*} [Group G] {x : G}
    (hx : ∀ g : G, g ∈ Subgroup.zpowers x) {m : ℕ} (hcard : Nat.card G = 2 ^ (m + 2))
    {c : G} (hc : c * c = 1) {M : Subgroup G} (hM : M.index = 2) :
    c ∈ M := by

  have hzt : Subgroup.zpowers x = ⊤ := eq_top_iff.mpr fun g _ => hx g
  have hord : orderOf x = 2 ^ (m + 2) := by
    rw [← Nat.card_zpowers, hzt, Subgroup.card_top, hcard]

  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hx c)
  have h2n : x ^ (n + n) = 1 := by
    rw [zpow_add, hn]
    exact hc
  have hdvd : ((2 : ℤ) ^ (m + 2)) ∣ (n + n) := by
    have h := orderOf_dvd_iff_zpow_eq_one.mpr h2n
    rw [hord] at h
    exact_mod_cast h
  obtain ⟨s, hs⟩ : ((2 : ℤ) ^ (m + 1)) ∣ n := by
    obtain ⟨t, ht⟩ := hdvd
    refine ⟨t, ?_⟩
    have hp2 : ((2 : ℤ) ^ (m + 2)) = 2 ^ (m + 1) * 2 := pow_succ 2 (m + 1)
    rw [hp2] at ht
    have ht' : n + n = 2 ^ (m + 1) * t + 2 ^ (m + 1) * t := by
      rw [ht]
      ring
    linarith

  have hcsq : c = x ^ ((2 : ℤ) ^ m * s) * x ^ ((2 : ℤ) ^ m * s) := by
    rw [← zpow_add, ← hn]
    congr 1
    rw [hs]
    ring

  haveI : M.Normal := Subgroup.normal_of_index_eq_two hM
  have hquot : ∀ z : G ⧸ M, z * z = 1 := by
    intro z
    have h := pow_card_eq_one' (x := z)
    rwa [← Subgroup.index_eq_card, hM, pow_two] at h
  have hc1 : ((c : G ⧸ M)) = 1 := by
    rw [hcsq, QuotientGroup.mk_mul]
    exact hquot _
  exact (QuotientGroup.eq_one_iff c).mp hc1

theorem gapsw7_x2c_finrank_fixedField_eq_index {E : Type*} [Field E] [Algebra ℚ E]
    [FiniteDimensional ℚ E] [IsGalois ℚ E] (M : Subgroup (E ≃ₐ[ℚ] E)) :
    finrank ℚ ↥(IntermediateField.fixedField M) = M.index := by
  haveI : Finite (E ≃ₐ[ℚ] E) := Nat.finite_of_card_ne_zero (by
    rw [IsGalois.card_aut_eq_finrank ℚ E]
    exact Module.finrank_pos.ne')
  have h1 : finrank ℚ ↥(IntermediateField.fixedField M) *
      finrank ↥(IntermediateField.fixedField M) E = finrank ℚ E :=
    Module.finrank_mul_finrank ℚ ↥(IntermediateField.fixedField M) E
  rw [IntermediateField.finrank_fixedField_eq_card] at h1
  have h2 : Nat.card ↥M * M.index = Nat.card (E ≃ₐ[ℚ] E) := Subgroup.card_mul_index M
  rw [IsGalois.card_aut_eq_finrank ℚ E] at h2
  have hM0 : 0 < Nat.card ↥M := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hM0 ?_
  rw [h1, ← h2]
  exact mul_comm _ _

theorem gapsw7_x2c_eq_of_fixedField_eq {E : Type*} [Field E] [Algebra ℚ E]
    [FiniteDimensional ℚ E] {M₁ M₂ : Subgroup (E ≃ₐ[ℚ] E)}
    (h : IntermediateField.fixedField M₁ = IntermediateField.fixedField M₂) :
    M₁ = M₂ := by
  have h₁ := IntermediateField.fixingSubgroup_fixedField M₁
  have h₂ := IntermediateField.fixingSubgroup_fixedField M₂
  rw [← h₁, ← h₂, h]

end FLT.Gapsw7X2cTwoGroupCyclicReduction
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

end
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

section

open Module

attribute [local instance] FractionRing.liftAlgebra

namespace NumberField
p2m_export "NumberField" "abs_discr_gt_two integralBasis_apply discr mk integralBasis to_finiteDimensional RingOfIntegers RingOfIntegers.basis absNorm_differentIdeal discr_ne_zero to_charZero RingOfIntegers.algebraMap.injective integralBasis_repr_apply coe_discr"
p2m_open "NumberField"

p2m_open_scoped "NumberField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.NumberField"

variable (K : Type*) [Field K] [NumberField K]

def IsUnramifiedOutside (S : Set ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → q ∉ S → ∀ (P : Ideal (𝓞 K)) [P.IsMaximal], (q : 𝓞 K) ∈ P →
    Algebra.IsUnramifiedAt ℤ P

theorem prime_mem_of_dvd_discr_of_isUnramifiedOutside {S : Set ℕ}
    (hKS : IsUnramifiedOutside K S) {q : ℕ} (hq : q.Prime) (hdvd : q ∣ (discr K).natAbs) :
    q ∈ S :=
  prime_mem_of_dvd_discr_of_forall_isUnramifiedAt K S hKS hq hdvd

end NumberField
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

end
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

section

open Module

namespace QuadParam

def RamifiedAt (d : ℤ) (q : ℕ) : Prop :=
  if q = 2 then d % 4 ≠ 1 else (q : ℤ) ∣ d

def UnramifiedOutside (d : ℤ) (ℓ : ℕ) : Prop :=
  Squarefree d ∧ d ≠ 1 ∧ ∀ q : ℕ, q.Prime → q ≠ ℓ → ¬ RamifiedAt d q

theorem ramifiedAt_two_iff (d : ℤ) : RamifiedAt d 2 ↔ d % 4 ≠ 1 := by
  simp [RamifiedAt]

theorem ramifiedAt_of_ne_two_iff (d : ℤ) {q : ℕ} (hq : q ≠ 2) :
    RamifiedAt d q ↔ (q : ℤ) ∣ d := by
  simp [RamifiedAt, hq]

theorem not_two_dvd_of_emod_four_eq_one {d : ℤ} (h4 : d % 4 = 1) : ¬ (2 : ℤ) ∣ d := by
  intro h2
  omega

theorem eq_neg_three_of_unramifiedOutside_three {d : ℤ}
    (hd : UnramifiedOutside d 3) : d = -3 := by
  obtain ⟨hsq, hd1, hram⟩ := hd

  have h4 : d % 4 = 1 := by
    have h := hram 2 Nat.prime_two (by norm_num)
    rw [ramifiedAt_two_iff] at h
    exact not_not.mp h

  have h2 : ¬ (2 : ℤ) ∣ d := not_two_dvd_of_emod_four_eq_one h4

  have hd0 : d ≠ 0 := hsq.ne_zero
  have hdnat0 : d.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hd0

  have huniq : ∀ {p : ℕ}, p.Prime → p ∣ d.natAbs → p = 3 := by
    intro p hp hpd
    have hpd' : (p : ℤ) ∣ d := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hpd)
    by_contra hp3
    rcases eq_or_ne p 2 with rfl | hp2
    · exact h2 (by exact_mod_cast hpd')
    · exact hram p hp hp3 ((ramifiedAt_of_ne_two_iff d hp2).mpr hpd')

  have hpow : d.natAbs = 3 ^ d.natAbs.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd hdnat0 huniq

  have hsqnat : Squarefree d.natAbs := Int.squarefree_natAbs.mpr hsq
  have hk1 : d.natAbs.primeFactorsList.length ≤ 1 := by
    by_contra hk
    rw [not_le] at hk
    have h9 : (3 : ℕ) * 3 ∣ d.natAbs := by
      rw [hpow]
      have h92 : (3 : ℕ) ^ 2 ∣ 3 ^ d.natAbs.primeFactorsList.length := pow_dvd_pow 3 hk
      simpa [pow_two] using h92
    exact (Nat.isUnit_iff.not.mpr (by norm_num)) (hsqnat 3 h9)

  have hk0 : d.natAbs.primeFactorsList.length ≠ 0 := by
    intro hk
    rw [hk, pow_zero] at hpow

    rcases Int.natAbs_eq d with h | h <;> rw [hpow] at h
    · exact hd1 (by simpa using h)
    ·
      omega

  have hk : d.natAbs.primeFactorsList.length = 1 :=
    le_antisymm hk1 (Nat.one_le_iff_ne_zero.mpr hk0)
  rw [hk, pow_one] at hpow

  rcases Int.natAbs_eq d with h | h <;> rw [hpow] at h <;> omega

theorem squarefree_of_natAbs_eq_prime {d : ℤ} {n : ℕ} (hdn : d.natAbs = n) (hn : n.Prime) :
    Squarefree d := by
  refine (Int.prime_iff_natAbs_prime.mpr ?_).squarefree
  rw [hdn]
  exact hn

theorem unramifiedOutside_neg_three : UnramifiedOutside (-3) 3 := by
  refine ⟨squarefree_of_natAbs_eq_prime (by decide) Nat.prime_three, by decide, ?_⟩
  intro q hq hq3
  rcases eq_or_ne q 2 with rfl | hq2
  · rw [ramifiedAt_two_iff]; decide
  · rw [ramifiedAt_of_ne_two_iff _ hq2]
    intro hdvd

    have hdvd' : q ∣ (3 : ℕ) := by
      have h := Int.natAbs_dvd_natAbs.mpr hdvd
      simpa using h
    exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdvd')

end QuadParam
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

namespace MonoidHom
p2m_export "MonoidHom" "map_neg inl inr range comap_bot mul mk' mem_range ext mk id"
p2m_open "MonoidHom"

end MonoidHom
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

namespace NumberField
p2m_export "NumberField" "abs_discr_gt_two integralBasis_apply discr mk integralBasis to_finiteDimensional RingOfIntegers RingOfIntegers.basis absNorm_differentIdeal discr_ne_zero to_charZero RingOfIntegers.algebraMap.injective integralBasis_repr_apply coe_discr"
p2m_open "NumberField"

p2m_open_scoped "NumberField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.NumberField"

variable (K : Type*) [Field K] [NumberField K]

theorem exists_natAbs_discr_eq_three_pow_of_isUnramifiedOutside
    (hdeg : 1 < finrank ℚ K) (hK : IsUnramifiedOutside K {3}) :
    ∃ k : ℕ, 1 ≤ k ∧ (discr K).natAbs = 3 ^ k := by
  have hne : (discr K).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero K)

  have huniq : ∀ {p : ℕ}, p.Prime → p ∣ (discr K).natAbs → p = 3 := by
    intro p hp hpd
    simpa using prime_mem_of_dvd_discr_of_isUnramifiedOutside K hK hp hpd
  refine ⟨(discr K).natAbs.primeFactorsList.length, ?_,
    Nat.eq_prime_pow_of_unique_prime_dvd hne huniq⟩

  by_contra hk
  have h0 : (discr K).natAbs.primeFactorsList.length = 0 := by omega
  have h1 : (discr K).natAbs = 1 := by
    have hp := Nat.eq_prime_pow_of_unique_prime_dvd hne huniq
    rwa [h0, pow_zero] at hp
  have h2 : (2 : ℤ) < |discr K| := abs_discr_gt_two (K := K) hdeg
  rcases Int.natAbs_eq (discr K) with hd | hd <;> rw [h1] at hd <;> rw [hd] at h2 <;>
    norm_num at h2

def QuadraticDiscriminantTameAt (q : ℕ) : Prop :=
  finrank ℚ K = 2 → q.Prime → q ≠ 2 → ¬ ((q : ℤ) ^ 2 ∣ discr K)

theorem natAbs_discr_eq_three_of_quadratic_of_isUnramifiedOutside
    (hdeg : finrank ℚ K = 2) (hK : IsUnramifiedOutside K {3})
    (htame : QuadraticDiscriminantTameAt K 3) :
    (discr K).natAbs = 3 := by
  obtain ⟨k, hk1, hk⟩ :=
    exists_natAbs_discr_eq_three_pow_of_isUnramifiedOutside K (by omega) hK

  have hk2 : k < 2 := by
    by_contra hk2
    rw [not_lt] at hk2
    refine htame hdeg Nat.prime_three (by norm_num) ?_
    have h9 : (3 : ℕ) ^ 2 ∣ (discr K).natAbs := by
      rw [hk]; exact pow_dvd_pow 3 hk2
    have h10 : ((3 : ℕ) ^ 2 : ℤ) ∣ discr K :=
      Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h9)
    exact_mod_cast h10

  have hk' : k = 1 := by omega
  rw [hk', pow_one] at hk
  exact hk

end NumberField
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

end
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

section

noncomputable section

p2m_open "NumberField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.NumberField IntermediateField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField Module"

namespace CyclotomicCompositumUnramified

local notation "ℚ̄" => AlgebraicClosure ℚ

local instance instNumberFieldIntermediateHsupP (E : IntermediateField ℚ ℚ̄)
    [FiniteDimensional ℚ E] : NumberField ↥E where
  to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ ↥E).injective
  to_finiteDimensional := ‹_›

theorem isUnramifiedOutside_of_le {K L : IntermediateField ℚ ℚ̄} (hle : K ≤ L)
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ L]
    {S : Set ℕ} (hL : IsUnramifiedOutside ↥L S) : IsUnramifiedOutside ↥K S := by
  intro q hq hqS P' hP'max hqP'

  letI : Algebra ↥K ↥L := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ ↥K ↥L := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : FaithfulSMul (𝓞 ↥K) (𝓞 ↥L) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingOfIntegers.algebraMap.injective ↥K ↥L)

  obtain ⟨P, hPmax, hPover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 ↥L) P'
  haveI := hPmax
  haveI := hPover

  have hqP : ((q : ℕ) : 𝓞 ↥L) ∈ P := by
    have h1 : algebraMap (𝓞 ↥K) (𝓞 ↥L) ((q : ℕ) : 𝓞 ↥K) ∈ P :=
      (Ideal.mem_of_liesOver P P' ((q : ℕ) : 𝓞 ↥K)).mp hqP'
    rwa [map_natCast] at h1

  haveI : Algebra.IsUnramifiedAt ℤ P := hL q hq hqS P hqP
  exact Algebra.IsUnramifiedAt.of_liesOver ℤ P' P

section Cyclotomic

variable {N : ℕ} {ζ : ℚ̄}

end Cyclotomic
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

end CyclotomicCompositumUnramified
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

end
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

end
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

section

open Module Polynomial

p2m_open_scoped "IntermediateField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

namespace QuadExt

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

theorem eq_zero_of_smul_one_add_smul_eq_zero {x : L}
    (hx : x ∉ Set.range (algebraMap F L)) {a b : F} (h : a • (1 : L) + b • x = 0) :
    a = 0 ∧ b = 0 := by
  simp only [Algebra.smul_def, mul_one] at h
  have hb : b = 0 := by
    by_contra hb
    have hbL : algebraMap F L b ≠ 0 := fun hc =>
      hb ((algebraMap F L).injective (by rw [hc, _root_.map_zero]))
    refine hx ⟨-a / b, ?_⟩
    rw [map_div₀, _root_.map_neg, div_eq_iff hbL]
    linear_combination -h
  subst hb
  rw [_root_.map_zero, zero_mul, add_zero] at h
  exact ⟨(algebraMap F L).injective (by rw [h, _root_.map_zero]), rfl⟩

theorem exists_relation_of_finrank_eq_two (hrank : finrank F L = 2) (u v w : L) :
    ∃ a b c : F, a • u + b • v + c • w = 0 ∧ ¬(a = 0 ∧ b = 0 ∧ c = 0) := by
  have hfd : FiniteDimensional F L := Module.finite_of_finrank_pos (by omega)
  have hnli : ¬ LinearIndependent F ![u, v, w] := by
    intro hli
    have hcard := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hnli
  refine ⟨g 0, g 1, g 2, ?_, ?_⟩
  · simpa [Fin.sum_univ_three] using hg
  · rintro ⟨h0, h1, h2⟩
    fin_cases i <;> simp_all

theorem exists_eq_smul_one_add_smul_of_finrank_eq_two (hrank : finrank F L = 2) {x : L}
    (hx : x ∉ Set.range (algebraMap F L)) (z : L) :
    ∃ a b : F, z = a • (1 : L) + b • x := by
  obtain ⟨a, b, c, hrel, hne⟩ := exists_relation_of_finrank_eq_two hrank 1 x z
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    rw [zero_smul, add_zero] at hrel
    obtain ⟨ha, hb⟩ := eq_zero_of_smul_one_add_smul_eq_zero hx hrel
    exact absurd ⟨ha, hb, rfl⟩ hne
  · refine ⟨-(a / c), -(b / c), ?_⟩
    have hcL : algebraMap F L c ≠ 0 := fun hcc =>
      hc ((algebraMap F L).injective (by rw [hcc, _root_.map_zero]))
    simp only [Algebra.smul_def, mul_one] at hrel ⊢
    rw [_root_.map_neg, _root_.map_neg, map_div₀, map_div₀]
    field_simp
    linear_combination hrel

theorem exists_notMem_range_of_finrank_eq_two (hrank : finrank F L = 2) :
    ∃ x : L, x ∉ Set.range (algebraMap F L) := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  have hbij : Function.Bijective (Algebra.linearMap F L) :=
    ⟨fun _ _ h => (algebraMap F L).injective h, fun z => hall z⟩
  have := (LinearEquiv.ofBijective (Algebra.linearMap F L) hbij).finrank_eq
  rw [finrank_self] at this
  omega

theorem notMem_range_of_algebraMap_mul {x : L} (hx : x ∉ Set.range (algebraMap F L)) {c : F}
    (hc : c ≠ 0) : algebraMap F L c * x ∉ Set.range (algebraMap F L) := by
  rintro ⟨w, hw⟩
  exact hx ⟨c⁻¹ * w, by
    rw [map_mul, hw, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]⟩

theorem exists_sq_mem_range_of_finrank_eq_two (h2 : (2 : F) ≠ 0) (hrank : finrank F L = 2) :
    ∃ y : L, y ∉ Set.range (algebraMap F L) ∧ y ^ 2 ∈ Set.range (algebraMap F L) := by
  obtain ⟨x, hx⟩ := exists_notMem_range_of_finrank_eq_two hrank
  obtain ⟨c, b, hxx⟩ := exists_eq_smul_one_add_smul_of_finrank_eq_two hrank hx (x * x)
  simp only [Algebra.smul_def, mul_one] at hxx
  refine ⟨algebraMap F L 2 * x - algebraMap F L b, ?_, ⟨4 * c + b ^ 2, ?_⟩⟩
  · rintro ⟨w, hw⟩
    exact notMem_range_of_algebraMap_mul hx h2 ⟨w + b, by rw [map_add, hw]; ring⟩
  · rw [map_add, map_mul, map_pow, map_ofNat, map_ofNat]
    linear_combination (-4 : L) * hxx

private theorem _root_.Int.exists_squarefree_sq_mul {N : ℤ} (hN : N ≠ 0) :
    ∃ (m : ℤ) (d : ℤ), m ≠ 0 ∧ Squarefree d ∧ N = m ^ 2 * d := by
  obtain ⟨a, b, ha, hb, hab, hsq⟩ := Nat.sq_mul_squarefree_of_pos (Int.natAbs_pos.mpr hN)
  have hsqz : Squarefree ((a : ℤ)) := by
    rw [← Int.squarefree_natAbs, Int.natAbs_natCast]
    exact hsq
  rcases Int.natAbs_eq N with hN' | hN'
  · exact ⟨(b : ℤ), (a : ℤ), by exact_mod_cast hb.ne', hsqz,
      by rw [hN', ← hab]; push_cast; ring⟩
  · refine ⟨(b : ℤ), -(a : ℤ), by exact_mod_cast hb.ne', ?_,
      by rw [hN', ← hab]; push_cast; ring⟩
    rw [← Int.squarefree_natAbs, Int.natAbs_neg, Int.natAbs_natCast]
    exact hsq

p2m_alias "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Int.exists_squarefree_sq_mul" "Int.exists_squarefree_sq_mul"
private theorem _root_.Rat.exists_squarefree_sq_mul {r : ℚ} (hr : r ≠ 0) :
    ∃ (s : ℚ) (d : ℤ), s ≠ 0 ∧ Squarefree d ∧ r = s ^ 2 * (d : ℚ) := by
  have hden : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_nz
  have hnum : r.num ≠ 0 := Rat.num_ne_zero.mpr hr
  obtain ⟨m, d, hm, hd, hmd⟩ := Int.exists_squarefree_sq_mul
    (mul_ne_zero hnum (Int.natCast_ne_zero.mpr r.den_nz))
  refine ⟨(m : ℚ) / (r.den : ℚ), d, div_ne_zero (Int.cast_ne_zero.mpr hm) hden, hd, ?_⟩
  rw [div_pow, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hden)]
  have hclear : r * (r.den : ℚ) ^ 2 = ((r.num * (r.den : ℤ) : ℤ) : ℚ) := by
    push_cast
    rw [pow_two, ← mul_assoc, Rat.mul_den_eq_num]
  rw [hclear, hmd]
  push_cast
  ring

p2m_alias "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Rat.exists_squarefree_sq_mul" "Rat.exists_squarefree_sq_mul"
theorem exists_squarefree_param {L : Type*} [Field L] [Algebra ℚ L]
    (hrank : finrank ℚ L = 2) :
    ∃ (y : L) (d : ℤ), y ∉ Set.range (algebraMap ℚ L) ∧ Squarefree d ∧ d ≠ 1 ∧
      y ^ 2 = (d : L) := by
  obtain ⟨x, hx, r, hr⟩ := exists_sq_mem_range_of_finrank_eq_two (by norm_num) hrank

  have hx0 : x ≠ 0 := fun hc => hx ⟨0, by rw [_root_.map_zero, hc]⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [_root_.map_zero] at hr
    exact hx0 ((pow_eq_zero_iff (two_ne_zero)).mp hr.symm)
  obtain ⟨s, d, hs, hd, hsd⟩ := Rat.exists_squarefree_sq_mul hr0

  have hynot : algebraMap ℚ L s⁻¹ * x ∉ Set.range (algebraMap ℚ L) :=
    notMem_range_of_algebraMap_mul hx (inv_ne_zero hs)
  have hysq : (algebraMap ℚ L s⁻¹ * x) ^ 2 = (d : L) := by
    rw [mul_pow, ← map_pow, ← hr, hsd, ← map_mul,
      show s⁻¹ ^ 2 * (s ^ 2 * (d : ℚ)) = ((d : ℤ) : ℚ) by field_simp]
    exact map_intCast (algebraMap ℚ L) d
  refine ⟨algebraMap ℚ L s⁻¹ * x, d, hynot, hd, ?_, hysq⟩

  rintro rfl
  rw [show (((1 : ℤ) : L)) = 1 by norm_num] at hysq
  have hfac : (algebraMap ℚ L s⁻¹ * x - 1) * (algebraMap ℚ L s⁻¹ * x + 1) = 0 := by
    linear_combination hysq
  rcases mul_eq_zero.mp hfac with hcc | hcc
  · exact hynot ⟨1, by rw [map_one]; exact (sub_eq_zero.mp hcc).symm⟩
  · exact hynot ⟨-1, by rw [_root_.map_neg, map_one]; exact (eq_neg_of_add_eq_zero_left hcc).symm⟩

private theorem _root_.Int.eq_of_squarefree_of_eq_sq_mul {d₁ d₂ : ℤ} (h₁ : Squarefree d₁)
    (h₂ : Squarefree d₂) {b : ℚ} (h : (d₁ : ℚ) = b ^ 2 * (d₂ : ℚ)) :
    d₁ = d₂ := by

  have hZ : d₁ * (b.den : ℤ) ^ 2 = b.num ^ 2 * d₂ := by
    have hQ : (d₁ : ℚ) * (b.den : ℚ) ^ 2 = (b.num : ℚ) ^ 2 * (d₂ : ℚ) := by
      rw [h]
      calc b ^ 2 * (d₂ : ℚ) * (b.den : ℚ) ^ 2 = (b * (b.den : ℚ)) ^ 2 * (d₂ : ℚ) := by ring
        _ = (b.num : ℚ) ^ 2 * (d₂ : ℚ) := by rw [Rat.mul_den_eq_num]
    exact_mod_cast hQ

  have hcop : IsCoprime (b.num) ((b.den : ℤ)) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact b.reduced
  have hcop2 : IsCoprime (((b.den : ℤ)) ^ 2) (b.num ^ 2) := IsCoprime.pow hcop.symm
  have hdvd' : ((b.den : ℤ)) ^ 2 ∣ b.num ^ 2 * d₂ := ⟨d₁, by linear_combination -hZ⟩
  have hdvd₂ : ((b.den : ℤ)) ^ 2 ∣ d₂ := hcop2.dvd_of_dvd_mul_left hdvd'
  have hden1 : ((b.den : ℤ)) ^ 2 = 1 := by
    rcases Int.isUnit_iff.mp (h₂ (b.den : ℤ) (by rwa [← pow_two])) with hu | hu
    · rw [hu]; norm_num
    · exfalso; omega

  rw [hden1, mul_one] at hZ
  have hnum1 : b.num ^ 2 = 1 := by
    rcases Int.isUnit_iff.mp (h₁ b.num (by rw [← pow_two]; exact ⟨d₂, hZ⟩)) with hu | hu <;>
      rw [hu] <;> norm_num
  rw [hnum1, one_mul] at hZ
  exact hZ

p2m_alias "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Int.eq_of_squarefree_of_eq_sq_mul" "Int.eq_of_squarefree_of_eq_sq_mul"
theorem param_unique {L : Type*} [Field L] [Algebra ℚ L] (hrank : finrank ℚ L = 2)
    {y₁ y₂ : L} {d₁ d₂ : ℤ} (hy₁ : y₁ ∉ Set.range (algebraMap ℚ L))
    (hy₂ : y₂ ∉ Set.range (algebraMap ℚ L)) (hd₁ : Squarefree d₁) (hd₂ : Squarefree d₂)
    (hsq₁ : y₁ ^ 2 = ((d₁ : ℤ) : L)) (hsq₂ : y₂ ^ 2 = ((d₂ : ℤ) : L)) : d₁ = d₂ := by

  obtain ⟨a, b, hab⟩ := exists_eq_smul_one_add_smul_of_finrank_eq_two hrank hy₂ y₁
  simp only [Algebra.smul_def, mul_one] at hab

  have hb : b ≠ 0 := by
    rintro rfl
    rw [_root_.map_zero, zero_mul, add_zero] at hab
    exact hy₁ ⟨a, hab.symm⟩

  have hkey : (a ^ 2 + b ^ 2 * (d₂ : ℚ) - (d₁ : ℚ)) • (1 : L) + (2 * a * b) • y₂ = 0 := by
    simp only [Algebra.smul_def, mul_one, map_sub, map_add, map_mul, map_pow, map_ofNat,
      map_intCast]
    rw [← hsq₁, ← hsq₂, hab]
    ring
  obtain ⟨hconst, hcross⟩ := eq_zero_of_smul_one_add_smul_eq_zero hy₂ hkey

  have ha : a = 0 := by
    rcases mul_eq_zero.mp hcross with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · norm_num at h''
      · exact h''
    · exact absurd h' hb

  refine Int.eq_of_squarefree_of_eq_sq_mul hd₁ hd₂ (b := b) ?_
  rw [ha] at hconst
  linear_combination -hconst

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [Algebra.IsIntegral ℚ Ω]

theorem adjoin_eq_of_finrank_eq_two {K : IntermediateField ℚ Ω} (hrank : finrank ℚ K = 2)
    {y : Ω} (hyK : y ∈ K) (hy : y ∉ Set.range (algebraMap ℚ Ω)) : ℚ⟮y⟯ = K := by
  have hint : _root_.IsIntegral ℚ y := Algebra.IsIntegral.isIntegral y
  have hfd : FiniteDimensional ℚ K := Module.finite_of_finrank_pos (by omega)
  refine IntermediateField.eq_of_le_of_finrank_le
    (IntermediateField.adjoin_simple_le_iff.mpr hyK) ?_
  rw [hrank, IntermediateField.adjoin.finrank hint]
  exact (minpoly.two_le_natDegree_iff hint).mpr fun h => hy (RingHom.mem_range.mp h)

theorem intermediateField_eq_of_sq_eq {K₁ K₂ : IntermediateField ℚ Ω}
    (h₁ : finrank ℚ K₁ = 2) (h₂ : finrank ℚ K₂ = 2) {y₁ y₂ : Ω} (hy₁K : y₁ ∈ K₁)
    (hy₂K : y₂ ∈ K₂) (hy₁ : y₁ ∉ Set.range (algebraMap ℚ Ω)) (hsq : y₁ ^ 2 = y₂ ^ 2) :
    K₁ = K₂ := by

  have hy₁K₂ : y₁ ∈ K₂ := by
    have hfac : (y₁ - y₂) * (y₁ + y₂) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hfac with h | h
    · rw [sub_eq_zero.mp h]; exact hy₂K
    · rw [eq_neg_of_add_eq_zero_left h]; exact K₂.neg_mem hy₂K
  rw [← adjoin_eq_of_finrank_eq_two h₁ hy₁K hy₁, ← adjoin_eq_of_finrank_eq_two h₂ hy₁K₂ hy₁]

theorem intermediateField_eq_of_param_unramifiedOutside_three
    {K₁ K₂ : IntermediateField ℚ Ω} (h₁ : finrank ℚ K₁ = 2) (h₂ : finrank ℚ K₂ = 2)
    {y₁ y₂ : Ω} {d₁ d₂ : ℤ} (hy₁K : y₁ ∈ K₁) (hy₂K : y₂ ∈ K₂)
    (hy₁ : y₁ ∉ Set.range (algebraMap ℚ Ω)) (hsq₁ : y₁ ^ 2 = ((d₁ : ℤ) : Ω))
    (hsq₂ : y₂ ^ 2 = ((d₂ : ℤ) : Ω)) (hur₁ : QuadParam.UnramifiedOutside d₁ 3)
    (hur₂ : QuadParam.UnramifiedOutside d₂ 3) : K₁ = K₂ := by
  have e₁ : d₁ = -3 := QuadParam.eq_neg_three_of_unramifiedOutside_three hur₁
  have e₂ : d₂ = -3 := QuadParam.eq_neg_three_of_unramifiedOutside_three hur₂
  refine intermediateField_eq_of_sq_eq h₁ h₂ hy₁K hy₂K hy₁ ?_
  rw [hsq₁, hsq₂, e₁, e₂]

end QuadExt
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

end
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

section

p2m_open "Module NumberField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.NumberField"

open scoped Matrix

namespace QuadExt

section OrderDiscriminant

variable {K : Type*} [Field K] [Algebra ℚ K]

theorem linearIndependent_one_param {y : K} (hy : y ∉ Set.range (algebraMap ℚ K)) :
    LinearIndependent ℚ ![(1 : K), y] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_two] at hg
  obtain ⟨h0, h1⟩ := eq_zero_of_smul_one_add_smul_eq_zero hy (a := g 0) (b := g 1)
    (by simpa using hg)
  intro i
  fin_cases i <;> assumption

theorem span_one_param (hrank : finrank ℚ K = 2) {y : K}
    (hy : y ∉ Set.range (algebraMap ℚ K)) :
    ⊤ ≤ Submodule.span ℚ (Set.range ![(1 : K), y]) := by
  intro z _
  obtain ⟨a, b, hab⟩ := exists_eq_smul_one_add_smul_of_finrank_eq_two hrank hy z
  rw [hab]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

noncomputable def paramBasis (hrank : finrank ℚ K = 2) {y : K}
    (hy : y ∉ Set.range (algebraMap ℚ K)) : Basis (Fin 2) ℚ K :=
  Basis.mk (linearIndependent_one_param hy) (span_one_param hrank hy)

@[scoped simp] theorem paramBasis_apply_zero (hrank : finrank ℚ K = 2) {y : K}
    (hy : y ∉ Set.range (algebraMap ℚ K)) : paramBasis hrank hy 0 = 1 := by
  simp [paramBasis]

@[scoped simp] theorem paramBasis_apply_one (hrank : finrank ℚ K = 2) {y : K}
    (hy : y ∉ Set.range (algebraMap ℚ K)) : paramBasis hrank hy 1 = y := by
  simp [paramBasis]

theorem trace_eq_zero_of_sq_eq (hrank : finrank ℚ K = 2) {y : K}
    (hy : y ∉ Set.range (algebraMap ℚ K)) {q : ℚ} (hyq : y ^ 2 = algebraMap ℚ K q) :
    Algebra.trace ℚ K y = 0 := by
  classical
  set b := paramBasis hrank hy with hb
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace_fin_two]
  have h00 : Algebra.leftMulMatrix b y 0 0 = 0 := by
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    have hy0 : y * b 0 = b 1 := by
      rw [hb, paramBasis_apply_zero, paramBasis_apply_one, mul_one]
    rw [hy0, b.repr_self]
    simp
  have h11 : Algebra.leftMulMatrix b y 1 1 = 0 := by
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    have hy1 : y * b 1 = q • b 0 := by
      rw [hb, paramBasis_apply_zero, paramBasis_apply_one, ← sq, hyq, Algebra.smul_def,
        mul_one]
    rw [hy1, map_smul, b.repr_self]
    simp
  rw [h00, h11, add_zero]

theorem trace_one_eq_two (hrank : finrank ℚ K = 2) : Algebra.trace ℚ K (1 : K) = 2 := by
  have h := Algebra.trace_algebraMap (R := ℚ) (S := K) (1 : ℚ)
  rw [map_one] at h
  rw [h, hrank]
  norm_num

theorem discr_one_sq_param (hrank : finrank ℚ K = 2) {y : K}
    (hy : y ∉ Set.range (algebraMap ℚ K)) {d : ℤ} (hyd : y ^ 2 = (d : K)) :
    Algebra.discr ℚ ![(1 : K), y] = 4 * (d : ℚ) := by
  classical
  have hyq : y ^ 2 = algebraMap ℚ K ((d : ℤ) : ℚ) := by
    rw [hyd]; norm_num
  have htr1 : Algebra.trace ℚ K (1 : K) = 2 := trace_one_eq_two hrank
  have htry : Algebra.trace ℚ K y = 0 := trace_eq_zero_of_sq_eq hrank hy hyq
  have htryy : Algebra.trace ℚ K (y * y) = 2 * (d : ℚ) := by
    rw [← sq, hyq, Algebra.trace_algebraMap, hrank, nsmul_eq_mul]
    norm_num
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, one_mul, mul_one]
  rw [htr1, htry, htryy]
  ring

omit [Algebra ℚ K] in

theorem isIntegral_of_sq_eq_intCast {y : K} {d : ℤ} (hyd : y ^ 2 = (d : K)) :
    _root_.IsIntegral ℤ y := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C d, Polynomial.monic_X_pow_sub_C d (by norm_num), ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
    sub_eq_zero, hyd]
  exact (eq_intCast (algebraMap ℤ K) d).symm

end OrderDiscriminant
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

theorem exists_sq_mul_discr_eq {K : Type*} [Field K] [NumberField K]
    (hrank : finrank ℚ K = 2) {y : K} (hy : y ∉ Set.range (algebraMap ℚ K))
    {d : ℤ} (hd0 : d ≠ 0) (hyd : y ^ 2 = (d : K)) :
    ∃ c : ℤ, c ≠ 0 ∧ 4 * d = c ^ 2 * discr K := by
  classical

  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 := by
    rw [← Module.finrank_eq_card_basis (integralBasis K), hrank]
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Fin 2 := Fintype.equivFinOfCardEq hcard
  let B : Basis (Fin 2) ℚ K := (integralBasis K).reindex e

  let P : Matrix (Fin 2) (Fin 2) ℚ := B.toMatrix ![(1 : K), y]

  have hint : ∀ i j, _root_.IsIntegral ℤ (P i j) := by
    intro i j
    have hvj : _root_.IsIntegral ℤ (![(1 : K), y] j) := by
      fin_cases j
      · exact isIntegral_one
      · exact isIntegral_of_sq_eq_intCast hyd
    obtain ⟨Y, hY⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 K)).mp hvj
    have hP : P i j = (integralBasis K).repr (![(1 : K), y] j) (e.symm i) := by
      simp only [P, Basis.toMatrix_apply, B, Basis.repr_reindex_apply]
    rw [hP, ← hY, integralBasis_repr_apply]
    exact isIntegral_algebraMap

  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp (_root_.IsIntegral.det hint)
  rw [eq_intCast] at hc

  have hvec : ⇑B ᵥ* P.map (algebraMap ℚ K) = ![(1 : K), y] :=
    B.toMatrix_map_vecMul ![(1 : K), y]
  have hdiscr : Algebra.discr ℚ ![(1 : K), y] = P.det ^ 2 * Algebra.discr ℚ ⇑B := by
    conv_lhs => rw [← hvec]
    exact Algebra.discr_of_matrix_vecMul (⇑B) P
  have hBdiscr : Algebra.discr ℚ ⇑B = ((discr K : ℤ) : ℚ) := by
    rw [coe_discr]
    have hcoe : ⇑B = ⇑(integralBasis K) ∘ ⇑e.symm := by
      ext i
      simp [B, Basis.coe_reindex]
    rw [hcoe, Algebra.discr_reindex]

  have e1 : ((4 * d : ℤ) : ℚ) = 4 * (d : ℚ) := by push_cast; ring
  have e2 : ((c ^ 2 * discr K : ℤ) : ℚ) = (c : ℚ) ^ 2 * ((discr K : ℤ) : ℚ) := by
    push_cast; ring
  have hQ : ((4 * d : ℤ) : ℚ) = ((c ^ 2 * discr K : ℤ) : ℚ) := by
    rw [e1, e2, ← discr_one_sq_param hrank hy hyd, hdiscr, hBdiscr, ← hc]
  have hZ : 4 * d = c ^ 2 * discr K := Int.cast_injective hQ
  refine ⟨c, ?_, hZ⟩
  rintro rfl
  rw [pow_two, mul_zero, zero_mul] at hZ
  omega

end QuadExt
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.QuadExt"

namespace Nat p2m_export "Nat" "prime_three exists_eq_succ_of_ne_zero cast_ne_zero sq_mul_squarefree_of_pos dvd_prime_pow Prime.coprime_iff_not_dvd Coprime.isCoprime dvd_prime prime_dvd_prime_iff_eq Coprime card_pos finite_of_card_ne_zero Prime.dvd_of_dvd_pow dvd_one even_or_odd' Prime cast_injective card_zpowers primeFactorsList eq_prime_pow_of_unique_prime_dvd card_fin succ_sub_one one_le_iff_ne_zero eq_of_mul_eq_mul_right prime_two mul_eq_zero coprime_primes" end Nat
p2m_open_scoped "Nat" in
theorem Nat.eq_one_of_squarefree_of_sq {m n : ℕ} (hm : Squarefree m) (h : m = n ^ 2) :
    m = 1 := by
  have hu : IsUnit n := hm n ⟨1, by rw [h]; ring⟩
  rw [h, Nat.isUnit_iff.mp hu, one_pow]

namespace Int
p2m_export "Int" "prime_three natAbs_mul isUnit_iff range natAbs natAbs_pos natAbs_dvd_natAbs cast_ne_zero even_or_odd' cast_injective natAbs_natCast natCast_ne_zero squarefree_natAbs natAbs_pow natAbs_ne_zero isCoprime_iff_gcd_eq_one natAbs_eq dvd_natAbs natAbs_neg natAbs_of_nonneg prime_two prime_iff_natAbs_prime natCast_dvd_natCast exists_squarefree_sq_mul eq_of_squarefree_of_eq_sq_mul even_and_even_or_emod_four_eq_one sq_eq_one_or_four_of_sq_dvd_four_mul"
p2m_open "Int"

theorem param_eq_discr_of_natAbs_eq_three {d c D : ℤ} (hd : Squarefree d)
    (h : 4 * d = c ^ 2 * D) (hD : D.natAbs = 3) :
    D = d ∧ (d = 3 ∨ d = -3) := by

  have h4 : (4 : ℤ).natAbs = 4 := by norm_num
  have hnat : 4 * d.natAbs = c.natAbs ^ 2 * 3 := by
    have h' := congrArg Int.natAbs h
    rwa [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, hD, h4] at h'
  have hdsf : Squarefree d.natAbs := Int.squarefree_natAbs.mpr hd

  have h34 : Nat.Coprime 3 4 := by decide
  have hdvd3 : (3 : ℕ) ∣ 4 * d.natAbs := ⟨c.natAbs ^ 2, by omega⟩
  obtain ⟨m, hm⟩ := h34.dvd_of_dvd_mul_left hdvd3

  have hcm : c.natAbs ^ 2 = 4 * m := by omega
  have hmsf : Squarefree m := by
    rw [hm] at hdsf
    exact hdsf.of_mul_right

  have hdvd2 : (2 : ℕ) ∣ c.natAbs ^ 2 := ⟨2 * m, by omega⟩
  obtain ⟨k, hk⟩ := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd2
  have hmk : m = k ^ 2 := by
    have h2 : 4 * m = 4 * k ^ 2 := by rw [← hcm, hk]; ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  have hm1 : m = 1 := Nat.eq_one_of_squarefree_of_sq hmsf hmk

  have hdnat : d.natAbs = 3 := by omega
  have hk1 : k = 1 := by
    have hkk : 1 = k * k := by
      have := (hmk.symm.trans hm1).symm
      rwa [pow_two] at this
    exact Nat.dvd_one.mp ⟨k, hkk⟩
  have hcnat : c.natAbs = 2 := by omega

  have hc2 : c ^ 2 = 4 := by
    have h1 : ((c ^ 2).natAbs : ℤ) = c ^ 2 := Int.natAbs_of_nonneg (sq_nonneg c)
    rw [← h1, Int.natAbs_pow, hcnat]
    norm_num
  rw [hc2] at h
  exact ⟨by omega, by omega⟩

theorem param_eq_neg_three_of_emod_four {d D : ℤ} (hDd : D = d) (hd3 : d = 3 ∨ d = -3)
    (hstick : D % 4 = 0 ∨ D % 4 = 1) : d = -3 := by
  subst hDd
  omega

end Int
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.QuadExt"

namespace QuadExt

theorem param_eq_neg_three_of_isUnramifiedOutside_three {K : Type*} [Field K] [NumberField K]
    (hrank : finrank ℚ K = 2) (hK : IsUnramifiedOutside K {3})
    (htame : QuadraticDiscriminantTameAt K 3)
    (hstick : discr K % 4 = 0 ∨ discr K % 4 = 1)
    {y : K} (hy : y ∉ Set.range (algebraMap ℚ K)) {d : ℤ} (hd : Squarefree d)
    (hyd : y ^ 2 = (d : K)) :
    d = -3 ∧ discr K = -3 := by
  have habs : (discr K).natAbs = 3 :=
    natAbs_discr_eq_three_of_quadratic_of_isUnramifiedOutside K hrank hK htame
  obtain ⟨c, -, hrel⟩ := exists_sq_mul_discr_eq hrank hy hd.ne_zero hyd
  obtain ⟨hDd, hd3⟩ := Int.param_eq_discr_of_natAbs_eq_three hd hrel habs
  have hdneg : d = -3 := Int.param_eq_neg_three_of_emod_four hDd hd3 hstick
  exact ⟨hdneg, by rw [hDd, hdneg]⟩

end QuadExt
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.QuadExt"

namespace QuadExt

end QuadExt
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.QuadExt"

end
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.QuadExt"

section

open Module Polynomial

p2m_open_scoped "IntermediateField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField"

namespace QuadExt

theorem finrank_rat_eq {M : Type*} [AddCommGroup M] (i₁ i₂ : Module ℚ M) :
    @finrank ℚ M _ _ i₁ = @finrank ℚ M _ _ i₂ := by
  obtain rfl : i₁ = i₂ := Subsingleton.elim i₁ i₂
  rfl

theorem mem_range_algebraMap_rat_iff {R : Type*} [DivisionRing R] [Algebra ℚ R] {x : R} :
    x ∈ Set.range (algebraMap ℚ R) ↔ ∃ q : ℚ, (q : R) = x := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q, (eq_ratCast (algebraMap ℚ R) q).symm⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q, eq_ratCast (algebraMap ℚ R) q⟩

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω]

theorem coe_mem_range_algebraMap_iff {K : IntermediateField ℚ Ω} (y : ↥K) :
    (y : Ω) ∈ Set.range (algebraMap ℚ Ω) ↔ y ∈ Set.range (algebraMap ℚ ↥K) := by
  rw [mem_range_algebraMap_rat_iff, mem_range_algebraMap_rat_iff]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, Subtype.ext hq⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, congrArg Subtype.val hq⟩

theorem exists_squarefree_param_mem {K : IntermediateField ℚ Ω} (hrank : finrank ℚ K = 2) :
    ∃ (y : Ω) (d : ℤ), y ∈ K ∧ y ∉ Set.range (algebraMap ℚ Ω) ∧ Squarefree d ∧ d ≠ 1 ∧
      y ^ 2 = (d : Ω) := by
  obtain ⟨y, d, hy, hd, hd1, hsq⟩ :=
    exists_squarefree_param (L := ↥K) ((finrank_rat_eq _ _).trans hrank)
  refine ⟨(y : Ω), d, y.2, ?_, hd, hd1, ?_⟩
  · exact fun h => hy ((coe_mem_range_algebraMap_iff y).mp h)
  · exact_mod_cast congrArg Subtype.val hsq

theorem param_unique_mem {K : IntermediateField ℚ Ω} (hrank : finrank ℚ K = 2)
    {y₁ y₂ : Ω} {d₁ d₂ : ℤ} (hy₁K : y₁ ∈ K) (hy₂K : y₂ ∈ K)
    (hy₁ : y₁ ∉ Set.range (algebraMap ℚ Ω)) (hy₂ : y₂ ∉ Set.range (algebraMap ℚ Ω))
    (hd₁ : Squarefree d₁) (hd₂ : Squarefree d₂)
    (hsq₁ : y₁ ^ 2 = (d₁ : Ω)) (hsq₂ : y₂ ^ 2 = (d₂ : Ω)) : d₁ = d₂ := by
  refine param_unique (L := ↥K) ((finrank_rat_eq _ _).trans hrank)
    (y₁ := ⟨y₁, hy₁K⟩) (y₂ := ⟨y₂, hy₂K⟩)
    (fun h => hy₁ ((coe_mem_range_algebraMap_iff _).mpr h))
    (fun h => hy₂ ((coe_mem_range_algebraMap_iff _).mpr h)) hd₁ hd₂ ?_ ?_
  · exact Subtype.ext (by push_cast; exact hsq₁)
  · exact Subtype.ext (by push_cast; exact hsq₂)

theorem exists_squarefree_param_subtype {K : IntermediateField ℚ Ω}
    (hrank : finrank ℚ K = 2) :
    ∃ (y : ↥K) (d : ℤ), y ∉ Set.range (algebraMap ℚ ↥K) ∧ Squarefree d ∧ d ≠ 1 ∧
      y ^ 2 = ((d : ℤ) : ↥K) := by
  obtain ⟨y, d, hyK, hy, hd, hd1, hsq⟩ := exists_squarefree_param_mem hrank
  refine ⟨⟨y, hyK⟩, d, fun h => hy ((coe_mem_range_algebraMap_iff _).mpr h), hd, hd1, ?_⟩
  exact Subtype.ext (by push_cast; exact hsq)

variable [Algebra.IsIntegral ℚ Ω]

theorem intermediateField_eq_of_forall_param_unramifiedOutside_three
    {K₁ K₂ : IntermediateField ℚ Ω} (h₁ : finrank ℚ K₁ = 2) (h₂ : finrank ℚ K₂ = 2)
    (hur₁ : ∀ (y : Ω) (d : ℤ), y ∈ K₁ → y ∉ Set.range (algebraMap ℚ Ω) → Squarefree d →
      y ^ 2 = (d : Ω) → QuadParam.UnramifiedOutside d 3)
    (hur₂ : ∀ (y : Ω) (d : ℤ), y ∈ K₂ → y ∉ Set.range (algebraMap ℚ Ω) → Squarefree d →
      y ^ 2 = (d : Ω) → QuadParam.UnramifiedOutside d 3) :
    K₁ = K₂ := by
  obtain ⟨y₁, d₁, hy₁K, hy₁, hd₁, -, hsq₁⟩ := exists_squarefree_param_mem h₁
  obtain ⟨y₂, d₂, hy₂K, hy₂, hd₂, -, hsq₂⟩ := exists_squarefree_param_mem h₂
  exact intermediateField_eq_of_param_unramifiedOutside_three h₁ h₂ hy₁K hy₂K hy₁ hsq₁ hsq₂
    (hur₁ y₁ d₁ hy₁K hy₁ hd₁ hsq₁) (hur₂ y₂ d₂ hy₂K hy₂ hd₂ hsq₂)

end QuadExt
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.QuadExt"

end
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.QuadExt"

section

p2m_open "Module NumberField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.NumberField"

open scoped Matrix

namespace QuadExt

section HalfIntegral

variable {K : Type*} [Field K] [NumberField K]

theorem exists_int_eq_of_isIntegral_algebraMap {r : ℚ}
    (h : _root_.IsIntegral ℤ (algebraMap ℚ K r)) : ∃ n : ℤ, (n : ℚ) = r := by
  have hr : _root_.IsIntegral ℤ r :=
    (isIntegral_algebraMap_iff (algebraMap ℚ K).injective).mp h
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hr
  exact ⟨n, by rw [← hn, eq_intCast]⟩

theorem exists_add_self_eq_of_isIntegral (hrank : finrank ℚ K = 2) {y : K}
    (hy : y ∉ Set.range (algebraMap ℚ K)) {d : ℤ} (hd : Squarefree d)
    (hyd : y ^ 2 = (d : K)) {z : K} (hz : _root_.IsIntegral ℤ z) :
    ∃ a b : ℤ, z + z = (a : K) + (b : K) * y ∧ (4 : ℤ) ∣ a ^ 2 - b ^ 2 * d := by
  classical
  have hCinj : Function.Injective (algebraMap ℚ K) := (algebraMap ℚ K).injective
  have hd0 : d ≠ 0 := hd.ne_zero
  have hdQ0 : ((d : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd0

  have hyq : y ^ 2 = algebraMap ℚ K ((d : ℤ) : ℚ) := by
    rw [hyd]; norm_num
  have hyint : _root_.IsIntegral ℤ y := isIntegral_of_sq_eq_intCast hyd

  obtain ⟨p, q, hpq₀⟩ := exists_eq_smul_one_add_smul_of_finrank_eq_two hrank hy z
  have hpq : z = algebraMap ℚ K p + algebraMap ℚ K q * y := by
    rw [hpq₀, Algebra.smul_def, Algebra.smul_def, mul_one]

  have htr : Algebra.trace ℚ K z = p + p := by
    have h1 : Algebra.trace ℚ K (1 : K) = 2 := trace_one_eq_two hrank
    have h2 : Algebra.trace ℚ K y = 0 := trace_eq_zero_of_sq_eq hrank hy hyq
    rw [hpq₀, map_add, LinearMap.map_smul, LinearMap.map_smul, h1, h2, smul_zero, add_zero,
      smul_eq_mul]
    ring
  obtain ⟨a, ha⟩ : ∃ n : ℤ, (n : ℚ) = p + p := by
    have h1 : _root_.IsIntegral ℤ (Algebra.trace ℚ K z) := Algebra.isIntegral_trace (R := ℤ) hz
    rw [htr] at h1
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
    exact ⟨n, by rw [← hn, eq_intCast]⟩

  set z' : K := algebraMap ℚ K p - algebraMap ℚ K q * y with hz'def
  have hz'int : _root_.IsIntegral ℤ z' := by
    have hsum : z' = (a : K) - z := by
      rw [hz'def, hpq, show ((a : ℤ) : K) = algebraMap ℚ K ((a : ℤ) : ℚ) from
        (map_intCast (algebraMap ℚ K) a).symm, ha, map_add]
      ring
    rw [hsum]
    exact (eq_intCast (algebraMap ℤ K) a ▸ isIntegral_algebraMap).sub hz

  have hzz' : z * z' = algebraMap ℚ K (p ^ 2 - q ^ 2 * ((d : ℤ) : ℚ)) := by
    rw [hpq, hz'def]
    simp only [map_sub, map_mul, map_pow]
    rw [← hyq]
    ring
  obtain ⟨m, hm⟩ : ∃ n : ℤ, (n : ℚ) = p ^ 2 - q ^ 2 * ((d : ℤ) : ℚ) := by
    refine exists_int_eq_of_isIntegral_algebraMap (K := K) ?_
    rw [← hzz']
    exact hz.mul hz'int

  have hwy : (z - z') * y =
      algebraMap ℚ K (q * ((d : ℤ) : ℚ) + q * ((d : ℤ) : ℚ)) := by
    rw [hpq, hz'def]
    simp only [map_add, map_mul]
    rw [← hyq]
    ring
  obtain ⟨t, ht⟩ : ∃ n : ℤ, (n : ℚ) = q * ((d : ℤ) : ℚ) + q * ((d : ℤ) : ℚ) := by
    refine exists_int_eq_of_isIntegral_algebraMap (K := K) ?_
    rw [← hwy]
    exact (hz.sub hz'int).mul hyint

  have htZ : t ^ 2 = (a ^ 2 - 4 * m) * d := by
    have hsq : ((t ^ 2 : ℤ) : ℚ) = (((a ^ 2 - 4 * m) * d : ℤ) : ℚ) := by
      push_cast
      rw [ht, ha, hm]
      ring
    exact_mod_cast hsq
  have hddvd : d ∣ t := by
    refine (hd.dvd_pow_iff_dvd (n := 2) two_ne_zero).mp ⟨a ^ 2 - 4 * m, ?_⟩
    rw [htZ]; ring
  obtain ⟨b, hb⟩ := hddvd

  have hbq : (b : ℚ) = q + q := by
    refine mul_left_cancel₀ hdQ0 ?_
    have h2 : ((d * b : ℤ) : ℚ) = (t : ℚ) := by exact_mod_cast hb.symm
    push_cast at h2
    rw [h2, ht]
    ring
  refine ⟨a, b, ?_, ?_⟩
  ·
    rw [hpq, show ((a : ℤ) : K) = algebraMap ℚ K ((a : ℤ) : ℚ) from
      (map_intCast (algebraMap ℚ K) a).symm,
      show ((b : ℤ) : K) = algebraMap ℚ K ((b : ℤ) : ℚ) from
      (map_intCast (algebraMap ℚ K) b).symm, ha, hbq, map_add, map_add]
    ring
  ·
    refine ⟨m, ?_⟩
    have hcast : ((a ^ 2 - b ^ 2 * d : ℤ) : ℚ) = ((4 * m : ℤ) : ℚ) := by
      push_cast
      rw [ha, hbq, hm]
      ring
    exact_mod_cast hcast

end HalfIntegral
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.QuadExt"

private theorem _root_.Int.even_and_even_or_emod_four_eq_one {a b d : ℤ} (hd : Squarefree d)
    (h : (4 : ℤ) ∣ a ^ 2 - b ^ 2 * d) : ((2 : ℤ) ∣ a ∧ (2 : ℤ) ∣ b) ∨ d % 4 = 1 := by
  obtain ⟨e, he⟩ := h
  obtain ⟨k, hk⟩ := Int.even_or_odd' a
  obtain ⟨l, hl⟩ := Int.even_or_odd' b
  rcases hk with hk | hk <;> rcases hl with hl | hl
  ·
    exact Or.inl ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
  ·
    exfalso
    have hdd : d = 4 * (k * k - l * l * d - l * d - e) := by
      subst hk; subst hl
      linear_combination -he
    have h2u : IsUnit (2 : ℤ) := hd 2 ⟨k * k - l * l * d - l * d - e, by linarith⟩
    rcases Int.isUnit_iff.mp h2u with h | h <;> norm_num at h
  ·
    exfalso
    have h1 : (1 : ℤ) = 4 * (e - k * k - k + l * l * d) := by
      subst hk; subst hl
      linear_combination he
    omega
  ·
    refine Or.inr ?_
    have hdd : d = 1 + 4 * (k * k + k - l * l * d - l * d - e) := by
      subst hk; subst hl
      linear_combination -he
    obtain ⟨X, hX⟩ : ∃ X : ℤ, d = 1 + 4 * X := ⟨_, hdd⟩
    omega

p2m_alias "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Int.even_and_even_or_emod_four_eq_one" "Int.even_and_even_or_emod_four_eq_one"
private theorem _root_.Int.sq_eq_one_or_four_of_sq_dvd_four_mul {c d : ℤ} (hd : Squarefree d)
    (h : c ^ 2 ∣ 4 * d) : c ^ 2 = 1 ∨ c ^ 2 = 4 := by
  obtain ⟨k, hk⟩ := Int.even_or_odd' c
  rcases hk with hk | hk
  ·
    right
    have h4 : (4 : ℤ) * k ^ 2 ∣ 4 * d := by
      have hck : c ^ 2 = 4 * k ^ 2 := by rw [hk]; ring
      rwa [hck] at h
    have hk2 : k ^ 2 ∣ d := (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp h4
    have hku : IsUnit k := hd k (by rwa [← sq])
    rcases Int.isUnit_iff.mp hku with rfl | rfl <;> rw [hk] <;> ring
  ·
    left

    have hnat : c.natAbs ^ 2 ∣ 4 * d.natAbs := by
      have h1 : (c ^ 2).natAbs ∣ (4 * d).natAbs := Int.natAbs_dvd_natAbs.mpr h
      simpa [Int.natAbs_mul, Int.natAbs_pow] using h1
    have hodd : ¬ (2 : ℕ) ∣ c.natAbs := by omega
    have hcop : Nat.Coprime (c.natAbs ^ 2) 4 := by
      have h2 : Nat.Coprime c.natAbs 2 :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd |>.symm
      simpa using h2.pow (m := 2) (n := 2)
    have hcd : c.natAbs ^ 2 ∣ d.natAbs := hcop.dvd_of_dvd_mul_left hnat
    have hdsf : Squarefree d.natAbs := Int.squarefree_natAbs.mpr hd
    have hcu : IsUnit c.natAbs := hdsf c.natAbs (by rwa [← sq])
    have hc1 : c.natAbs = 1 := Nat.isUnit_iff.mp hcu
    have hpm : c = 1 ∨ c = -1 := by omega
    rcases hpm with rfl | rfl <;> norm_num

p2m_alias "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Int.sq_eq_one_or_four_of_sq_dvd_four_mul" "Int.sq_eq_one_or_four_of_sq_dvd_four_mul"
end QuadExt
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.QuadExt"

namespace NumberField
p2m_export "NumberField" "abs_discr_gt_two integralBasis_apply discr mk integralBasis to_finiteDimensional RingOfIntegers RingOfIntegers.basis absNorm_differentIdeal discr_ne_zero to_charZero RingOfIntegers.algebraMap.injective integralBasis_repr_apply coe_discr"
p2m_open "NumberField"

theorem quadraticDiscriminantTameAt (K : Type*) [Field K] [NumberField K] (q : ℕ) :
    QuadraticDiscriminantTameAt K q := by
  intro hrank hq hq2 hdvd

  obtain ⟨y, d, hy, hd, -, hyd⟩ := QuadExt.exists_squarefree_param hrank
  obtain ⟨c, -, hrel⟩ := QuadExt.exists_sq_mul_discr_eq hrank hy hd.ne_zero hyd

  have h4d : (q : ℤ) ^ 2 ∣ 4 * d := by
    rw [hrel]
    exact hdvd.mul_left _

  have hnat : q ^ 2 ∣ 4 * d.natAbs := by
    have h1 : ((q : ℤ) ^ 2).natAbs ∣ (4 * d).natAbs := Int.natAbs_dvd_natAbs.mpr h4d
    simpa [Int.natAbs_mul, Int.natAbs_pow] using h1

  have hcop : Nat.Coprime (q ^ 2) 4 := by
    have h2 : Nat.Coprime q 2 := (Nat.coprime_primes hq Nat.prime_two).mpr hq2
    simpa using h2.pow (m := 2) (n := 2)
  have hqd : q ^ 2 ∣ d.natAbs := hcop.dvd_of_dvd_mul_left hnat

  have hdsf : Squarefree d.natAbs := Int.squarefree_natAbs.mpr hd
  have hqu : IsUnit q := hdsf q (by rwa [← sq])
  exact hq.one_lt.ne' (Nat.isUnit_iff.mp hqu)

variable {K : Type*} [Field K] [NumberField K]

theorem exists_discr_eq_sq_mul_four_mul (hrank : finrank ℚ K = 2) {y : K}
    (hy : y ∉ Set.range (algebraMap ℚ K)) {d : ℤ} (hd : Squarefree d)
    (hyd : y ^ 2 = (d : K)) (hd4 : d % 4 ≠ 1) :
    ∃ e : ℤ, (discr K : ℤ) = e ^ 2 * (4 * d) := by
  classical
  have h20 : (2 : K) ≠ 0 := two_ne_zero

  let pb : Basis (Fin 2) ℚ K := QuadExt.paramBasis hrank hy
  have hpbcoe : ⇑pb = ![(1 : K), y] := by
    funext i
    fin_cases i <;> simp [pb]

  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 := by
    rw [← Module.finrank_eq_card_basis (integralBasis K), hrank]
  let e2 : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Fin 2 := Fintype.equivFinOfCardEq hcard
  let B : Basis (Fin 2) ℚ K := (integralBasis K).reindex e2

  let Q : Matrix (Fin 2) (Fin 2) ℚ := pb.toMatrix ⇑B

  have hint : ∀ i j, _root_.IsIntegral ℤ (Q i j) := by
    intro i j

    have hBj : _root_.IsIntegral ℤ (B j) := by
      have hBj' : B j = algebraMap (𝓞 K) K ((RingOfIntegers.basis K) (e2.symm j)) := by
        simp [B, Basis.reindex_apply, integralBasis_apply]
      rw [hBj']
      exact (IsIntegralClosure.isIntegral_iff (A := 𝓞 K)).mpr ⟨_, rfl⟩

    obtain ⟨a, b, hab, hcong⟩ :=
      QuadExt.exists_add_self_eq_of_isIntegral hrank hy hd hyd hBj
    rcases Int.even_and_even_or_emod_four_eq_one hd hcong with ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ | hco
    swap
    · exact absurd hco hd4

    have hBj2 : B j = (a' : K) + (b' : K) * y := by
      refine mul_left_cancel₀ h20 ?_
      rw [two_mul, two_mul, hab, ha', hb']
      push_cast
      ring

    have h0 : pb 0 = (1 : K) := by simp [hpbcoe]
    have h1 : pb 1 = y := by simp [hpbcoe]
    have hBj3 : B j = ((a' : ℤ) : ℚ) • pb 0 + ((b' : ℤ) : ℚ) • pb 1 := by
      rw [h0, h1, hBj2, Algebra.smul_def, Algebra.smul_def, mul_one, map_intCast, map_intCast]
    have hco2 : pb.repr (B j) =
        Finsupp.single 0 ((a' : ℤ) : ℚ) + Finsupp.single 1 ((b' : ℤ) : ℚ) := by
      rw [hBj3, map_add, map_smul, map_smul, Basis.repr_self, Basis.repr_self,
        Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, mul_one, smul_eq_mul, mul_one]
    show _root_.IsIntegral ℤ (pb.toMatrix (⇑B) i j)
    rw [Basis.toMatrix_apply, hco2, Finsupp.add_apply]
    refine _root_.IsIntegral.add ?_ ?_ <;>
      rw [Finsupp.single_apply] <;>
      split <;>
      first
        | exact eq_intCast (algebraMap ℤ ℚ) _ ▸ isIntegral_algebraMap
        | exact isIntegral_zero

  obtain ⟨N, hN⟩ := IsIntegrallyClosed.isIntegral_iff.mp (_root_.IsIntegral.det hint)
  rw [eq_intCast] at hN

  have hvec : ⇑pb ᵥ* Q.map (algebraMap ℚ K) = ⇑B := pb.toMatrix_map_vecMul ⇑B
  have hdiscr : Algebra.discr ℚ ⇑B = Q.det ^ 2 * Algebra.discr ℚ ⇑pb := by
    conv_lhs => rw [← hvec]
    exact Algebra.discr_of_matrix_vecMul (⇑pb) Q
  have hBdiscr : Algebra.discr ℚ ⇑B = ((discr K : ℤ) : ℚ) := by
    rw [coe_discr]
    have hcoe : ⇑B = ⇑(integralBasis K) ∘ ⇑e2.symm := by
      ext i
      simp [B, Basis.coe_reindex]
    rw [hcoe, Algebra.discr_reindex]
  have hpbdiscr : Algebra.discr ℚ ⇑pb = 4 * ((d : ℤ) : ℚ) := by
    rw [hpbcoe]
    exact QuadExt.discr_one_sq_param hrank hy hyd

  refine ⟨N, ?_⟩
  have hQrel : ((discr K : ℤ) : ℚ) = ((N ^ 2 * (4 * d) : ℤ) : ℚ) := by
    rw [← hBdiscr, hdiscr, hpbdiscr, ← hN]
    push_cast
    ring
  exact_mod_cast hQrel

theorem discr_emod_four_of_finrank_eq_two (hrank : finrank ℚ K = 2) :
    discr K % 4 = 0 ∨ discr K % 4 = 1 := by
  obtain ⟨y, d, hy, hd, -, hyd⟩ := QuadExt.exists_squarefree_param hrank
  by_cases hd4 : d % 4 = 1
  ·
    obtain ⟨c, -, hrel⟩ := QuadExt.exists_sq_mul_discr_eq hrank hy hd.ne_zero hyd
    have hcdvd : c ^ 2 ∣ 4 * d := ⟨discr K, hrel⟩
    rcases Int.sq_eq_one_or_four_of_sq_dvd_four_mul hd hcdvd with hc | hc
    ·
      left
      rw [hc, one_mul] at hrel
      omega
    ·
      right
      rw [hc] at hrel
      omega
  ·
    left
    obtain ⟨e, he⟩ := exists_discr_eq_sq_mul_four_mul hrank hy hd hyd hd4
    have h4 : (4 : ℤ) ∣ (discr K : ℤ) := ⟨e ^ 2 * d, by rw [he]; ring⟩
    omega

end NumberField
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.QuadExt"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map mk isIntegral_iff IsIntegral Affine.Point j"
p2m_open "WeierstrassCurve"

end WeierstrassCurve
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.QuadExt"

end
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.QuadExt"

section

p2m_open "Module NumberField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.NumberField"

namespace QuadExt

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω]

theorem param_eq_neg_three_of_isUnramifiedOutside_three_mem
    {K : IntermediateField ℚ Ω} [NumberField ↥K]
    (hrank : finrank ℚ K = 2)
    (hK : IsUnramifiedOutside ↥K {3})
    (htame : QuadraticDiscriminantTameAt ↥K 3)
    (hstick : discr ↥K % 4 = 0 ∨ discr ↥K % 4 = 1)
    {y : Ω} {d : ℤ} (hyK : y ∈ K) (hy : y ∉ Set.range (algebraMap ℚ Ω))
    (hd : Squarefree d) (hyd : y ^ 2 = (d : Ω)) :
    d = -3 := by

  obtain ⟨y₀, d₀, hy₀, hd₀, -, hsq₀⟩ := exists_squarefree_param_subtype hrank

  have hy₀' : y₀ ∉ Set.range (algebraMap ℚ ↥K) := fun h =>
    hy₀ (mem_range_algebraMap_rat_iff.mpr (mem_range_algebraMap_rat_iff.mp h))

  have hd₀neg : d₀ = -3 :=
    (param_eq_neg_three_of_isUnramifiedOutside_three (K := ↥K)
      ((finrank_rat_eq _ _).trans hrank) hK htame hstick hy₀' hd₀ hsq₀).1

  have hdd₀ : d = d₀ :=
    param_unique_mem hrank hyK y₀.2 hy
      (fun h => hy₀ ((coe_mem_range_algebraMap_iff y₀).mp h)) hd hd₀ hyd
      (by exact_mod_cast congrArg Subtype.val hsq₀)
  rw [hdd₀, hd₀neg]

theorem forall_param_unramifiedOutside_three_of_isUnramifiedOutside
    {K : IntermediateField ℚ Ω} [NumberField ↥K]
    (hrank : finrank ℚ K = 2)
    (hK : IsUnramifiedOutside ↥K {3})
    (htame : QuadraticDiscriminantTameAt ↥K 3)
    (hstick : discr ↥K % 4 = 0 ∨ discr ↥K % 4 = 1) :
    ∀ (y : Ω) (d : ℤ), y ∈ K → y ∉ Set.range (algebraMap ℚ Ω) → Squarefree d →
      y ^ 2 = (d : Ω) → QuadParam.UnramifiedOutside d 3 := by
  intro y d hyK hy hd hyd
  rw [param_eq_neg_three_of_isUnramifiedOutside_three_mem hrank hK htame hstick hyK hy hd hyd]
  exact QuadParam.unramifiedOutside_neg_three

theorem exists_mem_sq_eq_neg_three_of_isUnramifiedOutside_three
    {K : IntermediateField ℚ Ω} [NumberField ↥K]
    (hrank : finrank ℚ K = 2)
    (hK : IsUnramifiedOutside ↥K {3})
    (htame : QuadraticDiscriminantTameAt ↥K 3)
    (hstick : discr ↥K % 4 = 0 ∨ discr ↥K % 4 = 1) :
    ∃ y : Ω, y ∈ K ∧ y ∉ Set.range (algebraMap ℚ Ω) ∧ y ^ 2 = ((-3 : ℤ) : Ω) := by
  obtain ⟨y, d, hyK, hy, hd, -, hyd⟩ := exists_squarefree_param_mem hrank
  refine ⟨y, hyK, hy, ?_⟩
  rw [hyd,
    param_eq_neg_three_of_isUnramifiedOutside_three_mem hrank hK htame hstick hyK hy hd hyd]

theorem intermediateField_eq_of_isUnramifiedOutside_three [Algebra.IsIntegral ℚ Ω]
    {K₁ K₂ : IntermediateField ℚ Ω} [NumberField ↥K₁] [NumberField ↥K₂]
    (h₁ : finrank ℚ K₁ = 2) (h₂ : finrank ℚ K₂ = 2)
    (hK₁ : IsUnramifiedOutside ↥K₁ {3}) (hK₂ : IsUnramifiedOutside ↥K₂ {3})
    (htame₁ : QuadraticDiscriminantTameAt ↥K₁ 3)
    (htame₂ : QuadraticDiscriminantTameAt ↥K₂ 3)
    (hstick₁ : discr ↥K₁ % 4 = 0 ∨ discr ↥K₁ % 4 = 1)
    (hstick₂ : discr ↥K₂ % 4 = 0 ∨ discr ↥K₂ % 4 = 1) :
    K₁ = K₂ :=
  intermediateField_eq_of_forall_param_unramifiedOutside_three h₁ h₂
    (forall_param_unramifiedOutside_three_of_isUnramifiedOutside h₁ hK₁ htame₁ hstick₁)
    (forall_param_unramifiedOutside_three_of_isUnramifiedOutside h₂ hK₂ htame₂ hstick₂)

end QuadExt
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.QuadExt"

end
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.QuadExt"

section

p2m_open "Module NumberField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.NumberField"

namespace FLT
namespace Gapsw7X2bUniqueQuadraticOutsideThree

local instance gapsw7_x2b_isIntegralQbar :
    Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) := by
  have h : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    have h := AlgebraicClosure.isAlgebraic (k := ℚ)
    convert h using 2 <;> first | rfl | exact Subsingleton.elim _ _
  exact Algebra.IsAlgebraic.isIntegral

theorem gapsw7_x2b_quadratic_isUnramifiedOutside_three_unique
    {K₁ K₂ : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥K₁] [NumberField ↥K₂]
    (h₁ : finrank ℚ ↥K₁ = 2) (h₂ : finrank ℚ ↥K₂ = 2)
    (hK₁ : IsUnramifiedOutside ↥K₁ ({3} : Set ℕ))
    (hK₂ : IsUnramifiedOutside ↥K₂ ({3} : Set ℕ)) :
    K₁ = K₂ :=
  QuadExt.intermediateField_eq_of_isUnramifiedOutside_three h₁ h₂ hK₁ hK₂
    (NumberField.quadraticDiscriminantTameAt _ _)
    (NumberField.quadraticDiscriminantTameAt _ _)
    (NumberField.discr_emod_four_of_finrank_eq_two ((QuadExt.finrank_rat_eq _ _).trans h₁))
    (NumberField.discr_emod_four_of_finrank_eq_two ((QuadExt.finrank_rat_eq _ _).trans h₂))

theorem gapsw7_x2b_exists_mem_sq_eq_neg_three
    {K : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥K]
    (h : finrank ℚ ↥K = 2) (hK : IsUnramifiedOutside ↥K ({3} : Set ℕ)) :
    ∃ y : AlgebraicClosure ℚ, y ∈ K ∧
      y ∉ Set.range (algebraMap ℚ (AlgebraicClosure ℚ)) ∧
      y ^ 2 = ((-3 : ℤ) : AlgebraicClosure ℚ) :=
  QuadExt.exists_mem_sq_eq_neg_three_of_isUnramifiedOutside_three h hK
    (NumberField.quadraticDiscriminantTameAt _ _)
    (NumberField.discr_emod_four_of_finrank_eq_two ((QuadExt.finrank_rat_eq _ _).trans h))

end FLT.Gapsw7X2bUniqueQuadraticOutsideThree
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.QuadExt"
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.QuadExt"

end
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.QuadExt"

section

p2m_open "Module NumberField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.NumberField"

p2m_open_scoped "IntermediateField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField NumberField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.NumberField MatrixGroups"

namespace FLT
namespace Gapsw7X2dQuarticExclusionDischarge

open FLT.Gapsw7X2bUniqueQuadraticOutsideThree
open FLT.Gapsw7X2cTwoGroupCyclicReduction

theorem gapsw7_x2d_lift_fixedField_quadratic
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (hunr : IsUnramifiedOutside (↥F) ({3} : Set ℕ))
    {M : Subgroup (↥F ≃ₐ[ℚ] ↥F)} (hM : M.index = 2) :
    finrank ℚ ↥(IntermediateField.lift (IntermediateField.fixedField M)) = 2 ∧
      IsUnramifiedOutside ↥(IntermediateField.lift (IntermediateField.fixedField M))
        ({3} : Set ℕ) := by
  haveI : FiniteDimensional ℚ ↥(IntermediateField.lift (IntermediateField.fixedField M)) :=
    Module.Finite.equiv (IntermediateField.liftAlgEquiv (IntermediateField.fixedField M)).toLinearEquiv
  constructor
  · rw [← (IntermediateField.liftAlgEquiv (IntermediateField.fixedField M)).toLinearEquiv.finrank_eq]

    exact (gapsw7_x2c_finrank_fixedField_eq_index M).trans hM
  · exact CyclotomicCompositumUnramified.isUnramifiedOutside_of_le
      (IntermediateField.lift_le (IntermediateField.fixedField M)) hunr

set_option maxHeartbeats 3200000 in

theorem gapsw7_x2d_finrank_le_two_of_isUnramifiedOutside
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (hunr : IsUnramifiedOutside (↥F) ({3} : Set ℕ))
    (hdvd : finrank ℚ ↥F ∣ 16) :
    finrank ℚ ↥F ≤ 2 := by
  by_contra hgt
  push Not at hgt

  obtain ⟨j, hj4, hj⟩ : ∃ j, j ≤ 4 ∧ finrank ℚ ↥F = 2 ^ j := by
    have h16 : finrank ℚ ↥F ∣ 2 ^ 4 := by
      have h4 : (2 : ℕ) ^ 4 = 16 := by norm_num
      rw [h4]
      exact hdvd
    exact (Nat.dvd_prime_pow Nat.prime_two).mp h16
  have hj2 : 2 ≤ j := by
    rcases j with _ | _ | j'
    · rw [hj] at hgt
      norm_num at hgt
    · rw [hj] at hgt
      norm_num at hgt
    · omega
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩

  have hcardG : Nat.card (↥F ≃ₐ[ℚ] ↥F) = 2 ^ (m + 2) := by
    rw [(IsGalois.card_aut_eq_finrank ℚ ↥F).trans (QuadExt.finrank_rat_eq _ _)]
    exact hj
  haveI : Finite (↥F ≃ₐ[ℚ] ↥F) := Nat.finite_of_card_ne_zero (by
    rw [hcardG]
    positivity)
  haveI : Nontrivial (↥F ≃ₐ[ℚ] ↥F) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hcardG]
    calc (1 : ℕ) < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega))
  have hdvd16 : Nat.card (↥F ≃ₐ[ℚ] ↥F) ∣ 16 := by
    rw [hcardG]
    have h4 : (16 : ℕ) = 2 ^ 4 := by norm_num
    rw [h4]
    exact pow_dvd_pow 2 (by omega)

  rcases gapsw7_x2c_two_index_two_or_generated hdvd16 with
    ⟨M₁, M₂, hMne, hMi₁, hMi₂⟩ | ⟨x, hx⟩
  ·
    obtain ⟨hr₁, hu₁⟩ := gapsw7_x2d_lift_fixedField_quadratic F hunr hMi₁
    obtain ⟨hr₂, hu₂⟩ := gapsw7_x2d_lift_fixedField_quadratic F hunr hMi₂
    haveI : FiniteDimensional ℚ ↥(IntermediateField.lift (IntermediateField.fixedField M₁)) :=
      Module.finite_of_finrank_pos (by rw [hr₁]; norm_num)
    haveI : FiniteDimensional ℚ ↥(IntermediateField.lift (IntermediateField.fixedField M₂)) :=
      Module.finite_of_finrank_pos (by rw [hr₂]; norm_num)
    haveI : CharZero ↥(IntermediateField.lift (IntermediateField.fixedField M₁)) :=
      charZero_of_injective_algebraMap (algebraMap ℚ _).injective
    haveI : CharZero ↥(IntermediateField.lift (IntermediateField.fixedField M₂)) :=
      charZero_of_injective_algebraMap (algebraMap ℚ _).injective
    haveI : NumberField ↥(IntermediateField.lift (IntermediateField.fixedField M₁)) := ⟨⟩
    haveI : NumberField ↥(IntermediateField.lift (IntermediateField.fixedField M₂)) := ⟨⟩
    have heq := gapsw7_x2b_quadratic_isUnramifiedOutside_three_unique hr₁ hr₂ hu₁ hu₂
    have hff : IntermediateField.fixedField M₁ = IntermediateField.fixedField M₂ :=
      (IntermediateField.lift_inj _ _).mp heq
    exact hMne (gapsw7_x2c_eq_of_fixedField_eq hff)
  ·
    have hp : IsPGroup 2 (↥F ≃ₐ[ℚ] ↥F) := IsPGroup.of_card hcardG
    obtain ⟨M₀, hM₀⟩ : ∃ M : Subgroup (↥F ≃ₐ[ℚ] ↥F), IsCoatom M := by
      rcases IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup (↥F ≃ₐ[ℚ] ↥F)) with
        hbot | ⟨M, hM, -⟩
      · obtain ⟨g, hg⟩ := exists_ne (1 : ↥F ≃ₐ[ℚ] ↥F)
        have hgbot : g ∈ (⊥ : Subgroup (↥F ≃ₐ[ℚ] ↥F)) := by
          rw [hbot]
          exact Subgroup.mem_top g
        exact absurd (Subgroup.mem_bot.mp hgbot) hg
      · exact ⟨M, hM⟩
    have hMi : M₀.index = 2 :=
      FLT.ModThreeTwoGroupCommutativity.index_eq_two_of_isCoatom_of_isPGroup hp hM₀

    obtain ⟨hr₀, hu₀⟩ := gapsw7_x2d_lift_fixedField_quadratic F hunr hMi
    haveI : FiniteDimensional ℚ ↥(IntermediateField.lift (IntermediateField.fixedField M₀)) :=
      Module.finite_of_finrank_pos (by rw [hr₀]; norm_num)
    haveI : CharZero ↥(IntermediateField.lift (IntermediateField.fixedField M₀)) :=
      charZero_of_injective_algebraMap (algebraMap ℚ _).injective
    haveI : NumberField ↥(IntermediateField.lift (IntermediateField.fixedField M₀)) := ⟨⟩
    obtain ⟨y, hyK, -, hysq⟩ := gapsw7_x2b_exists_mem_sq_eq_neg_three hr₀ hu₀

    haveI : IsScalarTower ℚ (↥F) (AlgebraicClosure ℚ) :=
      IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    have hpoint : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (z : ↥F),
        algebraMap (↥F) (AlgebraicClosure ℚ) ((AlgEquiv.restrictNormalHom F τ) z) =
          τ (algebraMap (↥F) (AlgebraicClosure ℚ) z) :=
      fun τ z => AlgEquiv.restrictNormal_commutes τ F z
    have hcc : AlgEquiv.restrictNormalHom F complexConjugation *
        AlgEquiv.restrictNormalHom F complexConjugation = 1 := by
      rw [← map_mul, complexConjugation_mul_self, map_one]
    have hcmem : AlgEquiv.restrictNormalHom F complexConjugation ∈ M₀ :=
      gapsw7_x2c_sq_one_mem_of_index_two hx hcardG hcc hMi

    have hyF : y ∈ F := IntermediateField.lift_le (IntermediateField.fixedField M₀) hyK
    have hymem : (⟨y, hyF⟩ : ↥F) ∈ IntermediateField.fixedField M₀ :=
      (IntermediateField.mem_lift (⟨y, hyF⟩ : ↥F)).mp hyK
    rw [IntermediateField.mem_fixedField_iff] at hymem
    have hcfix : (AlgEquiv.restrictNormalHom F complexConjugation) ⟨y, hyF⟩ = ⟨y, hyF⟩ :=
      hymem _ hcmem

    have hQbar : complexConjugation y = y := by
      have h2 := hpoint complexConjugation ⟨y, hyF⟩
      rw [hcfix] at h2
      simp only [IntermediateField.algebraMap_apply] at h2
      exact h2.symm

    have hreal : (complexEmbedding y).im = 0 := by
      have h := complexEmbedding_complexConjugation y
      rw [hQbar] at h
      exact Complex.conj_eq_iff_im.mp h.symm
    have hsqC : (complexEmbedding y) ^ 2 = ((-3 : ℤ) : ℂ) := by
      rw [← map_pow, hysq, map_intCast]
    have hre := congrArg Complex.re hsqC
    rw [pow_two, Complex.mul_re, hreal] at hre
    simp only [mul_zero, sub_zero, Complex.intCast_re] at hre
    have hneg : ((-3 : ℤ) : ℝ) = -3 := by norm_num
    rw [hneg] at hre
    nlinarith [mul_self_nonneg (complexEmbedding y).re]

end FLT.Gapsw7X2dQuarticExclusionDischarge
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.QuadExt"
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.QuadExt"

end
p2m_reactivate "P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.ContinuousAlgHom P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.Additive P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.IntermediateField P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.QuadExt"

open FLT.Gapsw7X2dQuarticExclusionDischarge in
theorem solution
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [IsGalois ℚ F]
    (hunr : ∀ (P : Ideal (NumberField.RingOfIntegers F)) [P.IsMaximal],
      (3 : NumberField.RingOfIntegers F) ∉ P → Algebra.IsUnramifiedAt ℤ P)
    (hdvd : Module.finrank ℚ F ∣ 16) :
    Module.finrank ℚ F ≤ 2 := by
  haveI : NumberField ↥F := inferInstance
  have hunr' : NumberField.IsUnramifiedOutside (↥F) ({3} : Set ℕ) := by
    intro q hq hq3 P _ hqP
    refine hunr P (fun h3 => ?_)
    have hq3' : q ≠ 3 := by simpa using hq3
    have hcop : Nat.Coprime q 3 := (Nat.coprime_primes hq Nat.prime_three).mpr hq3'
    obtain ⟨a, b, hab⟩ := Nat.Coprime.isCoprime hcop |>.intCast (R := NumberField.RingOfIntegers ↥F)

    have h1 : (1 : NumberField.RingOfIntegers ↥F) ∈ P := by
      rw [← hab]
      exact P.add_mem (P.mul_mem_left _ (by exact_mod_cast hqP)) (P.mul_mem_left _ (by exact_mod_cast h3))
    exact (Ideal.IsMaximal.ne_top ‹_›) ((Ideal.eq_top_iff_one P).mpr h1)
  exact gapsw7_x2d_finrank_le_two_of_isUnramifiedOutside F hunr' hdvd

end S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen
end P2MW
export P2MW.S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen (solution)
