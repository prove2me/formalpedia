-- Prove2me | solution 1 for NumberField.LevelArith.exists_cocyclesTwo_conj_transport_continuousH2SrInflation_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/090984ae-ce73-5062-81a4-2a006d6418a7

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import Theorems.Thm_IntermediateField_exists_normal_isUnramifiedOutside_of_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_cocyclesTwo_conj_transport_continuousH2SrInflation_eq

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory groupCohomology ExtCitation NumberField P2MW.S_NumberField_LevelArith_exists_cocyclesTwo_conj_transport_continuousH2SrInflation_eq.NumberField IsDedekindDomain NumberField.LevelArith P2MW.S_NumberField_LevelArith_exists_cocyclesTwo_conj_transport_continuousH2SrInflation_eq.NumberField.LevelArith"
p2m_open_scoped "NumberField.LevelArith P2MW.S_NumberField_LevelArith_exists_cocyclesTwo_conj_transport_continuousH2SrInflation_eq.NumberField.LevelArith"
open scoped Pointwise

noncomputable section

local instance isAlgebraicQbar_st : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar_st : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance normalQbar_st : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

namespace NumberField
namespace LevelArith
p2m_export "NumberField.LevelArith" "sUnitsMax mem_sUnitsMax_iff sUnitsMaxStable mem_sUnitsMaxStable_iff smul_mem_sUnitsMaxStable sUnitsMaxRep sUnitsMaxRep.val sUnitsMaxRep.val_ρ"
namespace SigmaTransport
p2m_open "NumberField.LevelArith NumberField"

section Stable

variable (S : Finset Nat.Primes)

theorem mem_of_mem_of_normal (N : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ ↥N]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {x : AlgebraicClosure ℚ} (hx : x ∈ N) : σ x ∈ N := by
  have h := (IntermediateField.normal_iff_forall_map_le'.mp (inferInstance : Normal ℚ ↥N)) σ
  exact h ⟨x, hx, rfl⟩

theorem conj_mem_fixingSubgroup_of_normal (N : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ ↥N]
    (σ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hg : g ∈ N.fixingSubgroup) : σ⁻¹ * g * σ ∈ N.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff] at hg ⊢
  intro y hy
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hg _ (mem_of_mem_of_normal N σ hy)]
  exact σ.symm_apply_apply y

theorem smul_mem_sUnitsMax (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {x : (AlgebraicClosure ℚ)ˣ} (hx : x ∈ sUnitsMax S) :
    σ • x ∈ sUnitsMax S := by
  rw [mem_sUnitsMax_iff] at hx ⊢
  obtain ⟨⟨F, hF, hxF⟩, hval⟩ := hx
  obtain ⟨N, hFN, hN, hNn⟩ := IntermediateField.exists_normal_isUnramifiedOutside_of_le S F hF
  haveI := hNn
  refine ⟨⟨N, hN, ?_⟩, fun q hq A hA => ?_⟩
  · change σ • (x : AlgebraicClosure ℚ) ∈ N
    rw [AlgEquiv.smul_def]
    exact mem_of_mem_of_normal N σ (hFN hxF)
  ·
    have hA' : (σ⁻¹ • A).LiesOverPrime (q : ℕ) := by
      unfold ValuationSubring.LiesOverPrime at hA ⊢
      rw [ValuationSubring.mem_nonunits_iff_or] at hA ⊢
      refine hA.imp id fun h h' => h ?_
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv] at h'
      rwa [AlgEquiv.smul_def, map_inv₀, map_natCast] at h'
    obtain ⟨h1, h2⟩ := hval q hq (σ⁻¹ • A) hA'
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv] at h1 h2
    rw [Units.val_inv_eq_inv_val] at h2
    refine ⟨?_, ?_⟩
    · exact h1
    · rw [Units.val_inv_eq_inv_val]
      change (σ • (x : AlgebraicClosure ℚ))⁻¹ ∈ A
      rw [← smul_inv'']
      exact h2

variable (L : IntermediateField ℚ (AlgebraicClosure ℚ))
  (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ : ↥L ≃ₐ[ℚ] ↥L)
  (hστ : ∀ y : ↥L, σ (y : AlgebraicClosure ℚ) = ((τ y : ↥L) : AlgebraicClosure ℚ))

include hστ in

theorem conj_mem (s : ↥L.fixingSubgroup) : σ⁻¹ * (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * σ ∈ L.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have hs := (IntermediateField.mem_fixingSubgroup_iff _ _).mp s.2
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hστ ⟨y, hy⟩, hs _ (τ ⟨y, hy⟩).2, ← hστ ⟨y, hy⟩]
  exact σ.symm_apply_apply y

include hστ in
theorem conj_mem' (s : ↥L.fixingSubgroup) : σ * (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * σ⁻¹ ∈ L.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have hs := (IntermediateField.mem_fixingSubgroup_iff _ _).mp s.2

  have hy' : σ.symm y = ((τ.symm ⟨y, hy⟩ : ↥L) : AlgebraicClosure ℚ) := by
    apply σ.injective
    rw [AlgEquiv.apply_symm_apply, hστ, AlgEquiv.apply_symm_apply]
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
  change σ ((s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (σ.symm y)) = y
  rw [hy', hs _ (τ.symm ⟨y, hy⟩).2, ← hy']
  exact σ.apply_symm_apply y

def conjHom : ↥L.fixingSubgroup →* ↥L.fixingSubgroup where
  toFun s := ⟨σ⁻¹ * (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * σ, conj_mem L σ τ hστ s⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    simp only [Subgroup.coe_mul]
    group)

theorem coe_conjHom (s : ↥L.fixingSubgroup) :
    ((conjHom L σ τ hστ s : ↥L.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = σ⁻¹ * (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * σ := rfl

include hστ in
theorem smul_mem_sUnitsMaxStable {x : (AlgebraicClosure ℚ)ˣ} (hx : x ∈ sUnitsMaxStable S L) : σ • x ∈ sUnitsMaxStable S L := by
  rw [mem_sUnitsMaxStable_iff] at hx ⊢
  intro γ
  have h : (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • σ • x = σ • ((⟨σ⁻¹ * γ * σ, conj_mem L σ τ hστ γ⟩ : ↥L.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • x := by
    rw [← mul_smul, ← mul_smul]
    congr 1
    group
  rw [h]
  exact smul_mem_sUnitsMax S σ (hx _)

def sigmaMap : sUnitsMaxRep S L →ₗ[ℤ] sUnitsMaxRep S L where
  toFun m := ⟨Additive.ofMul (σ • sUnitsMaxRep.val S L m), smul_mem_sUnitsMaxStable S L σ τ hστ m.2⟩
  map_add' a b := Subtype.ext (by
    show Additive.ofMul (σ • sUnitsMaxRep.val S L (a + b)) = Additive.ofMul (σ • sUnitsMaxRep.val S L a) + Additive.ofMul (σ • sUnitsMaxRep.val S L b)
    rw [← ofMul_mul, ← smul_mul']
    rfl)
  map_smul' n a := Subtype.ext (by
    show Additive.ofMul (σ • sUnitsMaxRep.val S L (n • a)) = n • Additive.ofMul (σ • sUnitsMaxRep.val S L a)
    rw [← ofMul_zpow, ← smul_zpow']
    rfl)

theorem val_sigmaMap (m : sUnitsMaxRep S L) : sUnitsMaxRep.val S L (sigmaMap S L σ τ hστ m) = σ • sUnitsMaxRep.val S L m := rfl

theorem sigmaMap_ρ_conj (g : ↥L.fixingSubgroup) (m : sUnitsMaxRep S L) :
    sigmaMap S L σ τ hστ ((sUnitsMaxRep S L).ρ (conjHom L σ τ hστ g) m) = (sUnitsMaxRep S L).ρ g (sigmaMap S L σ τ hστ m) := by
  apply Subtype.ext
  apply Additive.toMul.injective
  show σ • sUnitsMaxRep.val S L ((sUnitsMaxRep S L).ρ (conjHom L σ τ hστ g) m) = sUnitsMaxRep.val S L ((sUnitsMaxRep S L).ρ g (sigmaMap S L σ τ hστ m))
  rw [sUnitsMaxRep.val_ρ, sUnitsMaxRep.val_ρ, val_sigmaMap, coe_conjHom, ← mul_smul, ← mul_smul]
  congr 1
  group

end Stable

end NumberField.LevelArith.SigmaTransport

end

noncomputable section

namespace NumberField
namespace LevelArith
p2m_export "NumberField.LevelArith" "sUnitsMax mem_sUnitsMax_iff sUnitsMaxStable mem_sUnitsMaxStable_iff smul_mem_sUnitsMaxStable sUnitsMaxRep sUnitsMaxRep.val sUnitsMaxRep.val_ρ"
namespace SigmaTransport
p2m_open "NumberField.LevelArith NumberField"

section Cochains

variable (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
  (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ : ↥L ≃ₐ[ℚ] ↥L)
  (hστ : ∀ y : ↥L, σ (y : AlgebraicClosure ℚ) = ((τ y : ↥L) : AlgebraicClosure ℚ))

def T₁ : (↥L.fixingSubgroup → (sUnitsMaxRep S L)) →ₗ[ℤ] (↥L.fixingSubgroup → (sUnitsMaxRep S L)) where
  toFun b s := sigmaMap S L σ τ hστ (b (conjHom L σ τ hστ s))
  map_add' a b := by funext s; simp only [Pi.add_apply, map_add]
  map_smul' n a := by funext s; simp only [Pi.smul_apply, map_zsmul, RingHom.id_apply]

def T₂ : (↥L.fixingSubgroup × ↥L.fixingSubgroup → (sUnitsMaxRep S L)) →ₗ[ℤ] (↥L.fixingSubgroup × ↥L.fixingSubgroup → (sUnitsMaxRep S L)) where
  toFun g p := sigmaMap S L σ τ hστ (g (conjHom L σ τ hστ p.1, conjHom L σ τ hστ p.2))
  map_add' a b := by funext p; simp only [Pi.add_apply, map_add]
  map_smul' n a := by funext p; simp only [Pi.smul_apply, map_zsmul, RingHom.id_apply]

theorem T₁_apply (b : ↥L.fixingSubgroup → (sUnitsMaxRep S L)) (s : ↥L.fixingSubgroup) : T₁ S L σ τ hστ b s = sigmaMap S L σ τ hστ (b (conjHom L σ τ hστ s)) := rfl

theorem T₂_apply (g : ↥L.fixingSubgroup × ↥L.fixingSubgroup → (sUnitsMaxRep S L)) (s t : ↥L.fixingSubgroup) :
    T₂ S L σ τ hστ g (s, t) = sigmaMap S L σ τ hστ (g (conjHom L σ τ hστ s, conjHom L σ τ hστ t)) := rfl

theorem T₂_d₁₂ (b : ↥L.fixingSubgroup → (sUnitsMaxRep S L)) : T₂ S L σ τ hστ ((d₁₂ (sUnitsMaxRep S L)).hom b) = (d₁₂ (sUnitsMaxRep S L)).hom (T₁ S L σ τ hστ b) := by
  funext p
  obtain ⟨s, t⟩ := p
  rw [T₂_apply, d₁₂_hom_apply, d₁₂_hom_apply, T₁_apply, T₁_apply, T₁_apply, map_add, map_sub, sigmaMap_ρ_conj, map_mul]

theorem isLevelConstantSr₁_T₁ {b : ↥L.fixingSubgroup → (sUnitsMaxRep S L)} (hb : IsLevelConstantSr₁ L.fixingSubgroup.subtype S b) :
    IsLevelConstantSr₁ L.fixingSubgroup.subtype S (T₁ S L σ τ hστ b) := by
  obtain ⟨F₁, hF₁, h⟩ := hb
  obtain ⟨N, hF₁N, hN, hNn⟩ := IntermediateField.exists_normal_isUnramifiedOutside_of_le S F₁ hF₁
  haveI := hNn
  refine ⟨N, hN, fun g s hs => ?_⟩
  rw [T₁_apply, T₁_apply, map_mul]
  congr 1
  apply h
  exact IntermediateField.fixingSubgroup_antitone hF₁N (conj_mem_fixingSubgroup_of_normal N σ _ hs)

end Cochains

section Level

variable (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
  (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ : ↥L ≃ₐ[ℚ] ↥L)
  (hστ : ∀ y : ↥L, σ (y : AlgebraicClosure ℚ) = ((τ y : ↥L) : AlgebraicClosure ℚ))
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ ↥F]

theorem conjHom_mem (s : ↥L.fixingSubgroup) (hs : s ∈ (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) : conjHom L σ τ hστ s ∈ (F.fixingSubgroup.comap L.fixingSubgroup.subtype) := by
  rw [Subgroup.mem_comap] at hs ⊢
  exact conj_mem_fixingSubgroup_of_normal F σ _ hs

def conjQuot : ↥L.fixingSubgroup ⧸ (F.fixingSubgroup.comap L.fixingSubgroup.subtype) →* ↥L.fixingSubgroup ⧸ (F.fixingSubgroup.comap L.fixingSubgroup.subtype) :=
  QuotientGroup.map _ _ (conjHom L σ τ hστ) (fun s hs => conjHom_mem L σ τ hστ F s hs)

theorem conjQuot_mk (s : ↥L.fixingSubgroup) :
    conjQuot L σ τ hστ F (s : ↥L.fixingSubgroup ⧸ (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) = ((conjHom L σ τ hστ s : ↥L.fixingSubgroup) : ↥L.fixingSubgroup ⧸ (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) := rfl

theorem sigmaMap_mem_invariants (m : (sUnitsMaxRep S L))
    (hm : m ∈ Representation.invariants ((sUnitsMaxRep S L).ρ.comp (F.fixingSubgroup.comap L.fixingSubgroup.subtype).subtype)) :
    sigmaMap S L σ τ hστ m ∈ Representation.invariants ((sUnitsMaxRep S L).ρ.comp (F.fixingSubgroup.comap L.fixingSubgroup.subtype).subtype) := by
  intro u
  have h := sigmaMap_ρ_conj S L σ τ hστ (u : ↥L.fixingSubgroup) m
  rw [MonoidHom.comp_apply, Subgroup.subtype_apply, ← h]
  congr 1
  exact hm ⟨conjHom L σ τ hστ u, conjHom_mem L σ τ hστ F _ u.2⟩

def psiSigma : Rep.res (conjQuot L σ τ hστ F) ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶ (sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype) :=
  Rep.ofHom ⟨(sigmaMap S L σ τ hστ).restrict (fun m hm => sigmaMap_mem_invariants S L σ τ hστ F m hm), fun g => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    refine LinearMap.ext fun z => Subtype.ext ?_
    exact sigmaMap_ρ_conj S L σ τ hστ g z.1⟩

theorem coe_psiSigma (z : (sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
    ((psiSigma S L σ τ hστ F).hom z : (sUnitsMaxRep S L)) = sigmaMap S L σ τ hστ (z : (sUnitsMaxRep S L)) := rfl

end Level

end NumberField.LevelArith.SigmaTransport

end

set_option maxHeartbeats 6400000 in
open NumberField.LevelArith.SigmaTransport in

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] (hF : F.IsUnramifiedOutside S)
    (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (τ : ↥L ≃ₐ[ℚ] ↥L) (hστ : ∀ y : ↥L, σ (y : AlgebraicClosure ℚ) = ((τ y : ↥L) : AlgebraicClosure ℚ))
    (a a' : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ))))
    (w w' : ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S (sUnitsMaxRep S L)))
    (ha : (a : (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L))) = continuousH2Srπ L.fixingSubgroup.subtype S _ w)
    (ha' : (a' : (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L))) = continuousH2Srπ L.fixingSubgroup.subtype S _ w')
    (hww' : ∀ s t s' t' : ↥L.fixingSubgroup, σ⁻¹ * (s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = s' → σ⁻¹ * (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = t' →
            sUnitsMaxRep.val S L ((w' : ↥L.fixingSubgroup × ↥L.fixingSubgroup → (sUnitsMaxRep S L)) (s, t)) =
              σ • sUnitsMaxRep.val S L ((w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → (sUnitsMaxRep S L)) (s', t')))
    (f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (haf : (a : (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)))
        = continuousH2SrInflation L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F hF (H2π _ f)) :
    ∃ fσ : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)),
      (∀ s t s' t' : ↥L.fixingSubgroup, σ⁻¹ * (s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = s' → σ⁻¹ * (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = t' →
        sUnitsMaxRep.val S L ((fσ ((s : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)), (t : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)
          = σ • sUnitsMaxRep.val S L ((f ((s' : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)), (t' : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)) ∧
      (a' : (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)))
        = continuousH2SrInflation L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F hF (H2π _ fσ) := by

  obtain ⟨fσ, hfσ⟩ : ∃ fσ : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)),
      ∀ s t : ↥L.fixingSubgroup, ((fσ ((s : ↥L.fixingSubgroup ⧸ (F.fixingSubgroup.comap L.fixingSubgroup.subtype)), (t : ↥L.fixingSubgroup ⧸ (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : (sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) : (sUnitsMaxRep S L))
        = sigmaMap S L σ τ hστ ((f (((conjHom L σ τ hστ s : ↥L.fixingSubgroup) : ↥L.fixingSubgroup ⧸ (F.fixingSubgroup.comap L.fixingSubgroup.subtype)), ((conjHom L σ τ hστ t : ↥L.fixingSubgroup) : ↥L.fixingSubgroup ⧸ (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) :
            (sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) : (sUnitsMaxRep S L)) := by
    refine ⟨mapCocycles₂ (conjQuot L σ τ hστ F) (psiSigma S L σ τ hστ F) f, fun s t => ?_⟩
    show (((mapCocycles₂ (conjQuot L σ τ hστ F) (psiSigma S L σ τ hστ F) f : cocycles₂ _) : _ → _) ((s : ↥L.fixingSubgroup ⧸ (F.fixingSubgroup.comap L.fixingSubgroup.subtype)), (t : ↥L.fixingSubgroup ⧸ (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : (sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)).1 = _
    rw [coe_mapCocycles₂]
    rfl
  refine ⟨fσ, fun s t s' t' hs ht => ?_, ?_⟩
  ·
    have hs' : conjHom L σ τ hστ s = s' := Subtype.ext hs
    have ht' : conjHom L σ τ hστ t = t' := Subtype.ext ht
    rw [hfσ s t, hs', ht']
    rfl
  ·

    have h1 : continuousH2Srπ L.fixingSubgroup.subtype S (sUnitsMaxRep S L)
        (levelInflateCocyclesSr₂ L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F hF f - w) = 0 := by
      rw [map_sub, ← continuousH2SrInflation_H2π, ← haf, ha, sub_self]
    rw [continuousH2Srπ_eq_zero_iff] at h1
    obtain ⟨b, hb, hdb⟩ := (mem_levelCoboundariesSr₂_iff _ _ _ _).mp h1

    have hLI : (levelInflateCocyclesSr₂ L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F hF fσ : ↥L.fixingSubgroup × ↥L.fixingSubgroup → (sUnitsMaxRep S L)) =
        T₂ S L σ τ hστ (levelInflateCocyclesSr₂ L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F hF f : ↥L.fixingSubgroup × ↥L.fixingSubgroup → (sUnitsMaxRep S L)) := by
      funext p
      obtain ⟨s, t⟩ := p
      rw [coe_levelInflateCocyclesSr₂, coe_levelInflateCocyclesSr₂, T₂_apply, levelInflate₂_apply, levelInflate₂_apply]
      exact hfσ s t
    have hw' : ((w' : ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S (sUnitsMaxRep S L))) : ↥L.fixingSubgroup × ↥L.fixingSubgroup → (sUnitsMaxRep S L)) = T₂ S L σ τ hστ ((w : ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S (sUnitsMaxRep S L))) : ↥L.fixingSubgroup × ↥L.fixingSubgroup → (sUnitsMaxRep S L)) := by
      funext p
      obtain ⟨s, t⟩ := p
      rw [T₂_apply]
      apply Subtype.ext
      apply Additive.toMul.injective
      exact hww' s t (conjHom L σ τ hστ s) (conjHom L σ τ hστ t) rfl rfl
    have h2 : ((levelInflateCocyclesSr₂ L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F hF fσ - w' : ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S (sUnitsMaxRep S L))) : ↥L.fixingSubgroup × ↥L.fixingSubgroup → (sUnitsMaxRep S L))
        ∈ levelCoboundariesSr₂ L.fixingSubgroup.subtype S (sUnitsMaxRep S L) := by
      rw [mem_levelCoboundariesSr₂_iff]
      refine ⟨T₁ S L σ τ hστ b, isLevelConstantSr₁_T₁ S L σ τ hστ hb, ?_⟩
      rw [← T₂_d₁₂, hdb, Submodule.coe_sub, Submodule.coe_sub, hLI, hw', map_sub]

    have h3 : continuousH2Srπ L.fixingSubgroup.subtype S (sUnitsMaxRep S L) (levelInflateCocyclesSr₂ L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F hF fσ) =
        continuousH2Srπ L.fixingSubgroup.subtype S (sUnitsMaxRep S L) w' := by
      rw [← sub_eq_zero, ← map_sub, continuousH2Srπ_eq_zero_iff]
      exact h2
    rw [ha', continuousH2SrInflation_H2π, h3]

end S_NumberField_LevelArith_exists_cocyclesTwo_conj_transport_continuousH2SrInflation_eq
end P2MW
export P2MW.S_NumberField_LevelArith_exists_cocyclesTwo_conj_transport_continuousH2SrInflation_eq (solution)
