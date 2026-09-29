-- Prove2me | solution 1 for LanglandsTunnell.Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/98821cb4-45f8-51b9-9a0c-e443013a42eb

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_LanglandsTunnell_C8Character
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one

namespace Deep
namespace NTSupply
p2m_export "Deep.NTSupply" "coprimeToModulus mem_coprimeToModulus_iff mem_narrowRaySet_iff narrowRaySubgroup narrowRaySubgroup_le_coprimeToModulus raySymbol hasFiniteMulSupport_raySymbol_factors raySymbolUnitsHom raySymbolHom raySymbolHom_apply principalUnit principalUnit_val principalUnit_mem_coprimeToModulus primeUnit primeUnit_val primeUnit_mem_coprimeToModulus raySymbol_primeUnit"
p2m_open "Deep.NTSupply Deep"
end Deep.NTSupply

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff relNormCTM"
p2m_open "HeckeCharacter"
end HeckeCharacter

namespace LanglandsTunnell
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"
end LanglandsTunnell.P2.Artin

namespace LanglandsTunnell
namespace P0
p2m_open "LanglandsTunnell"
end LanglandsTunnell.P0

namespace LanglandsTunnell
namespace P5
p2m_open "LanglandsTunnell"
end LanglandsTunnell.P5

namespace LanglandsTunnell
namespace P2
p2m_open "LanglandsTunnell.P2 LanglandsTunnell"
end LanglandsTunnell.P2

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

open NumberField IsDedekindDomain

open scoped Pointwise

section Transport

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]

private theorem inertia_smul_eq_bot (τ : G) (Q : Ideal S) (hI : Q.inertia G = ⊥) : (τ • Q).inertia G = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hg' : ∀ x : S, g • x - x ∈ τ • Q := fun x => hg x
  have hmem : τ⁻¹ * g * τ ∈ Q.inertia G := by
    intro x
    have hx := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 (hg' (τ • x))
    rw [smul_sub, inv_smul_smul, ← mul_smul, ← mul_smul] at hx
    exact hx
  rw [hI, Subgroup.mem_bot] at hmem
  have hgg : g = τ * (τ⁻¹ * g * τ) * τ⁻¹ := by group
  rw [hmem] at hgg
  simpa using hgg

private theorem eq_of_isArithFrobAt_of_inertia_eq_bot {σ σ' : G} {Q : Ideal S} (H : IsArithFrobAt R σ Q) (H' : IsArithFrobAt R σ' Q)
    (hI : Q.inertia G = ⊥) : σ = σ' := by
  have h := H.mul_inv_mem_inertia H'
  rw [hI, Subgroup.mem_bot] at h
  exact mul_inv_eq_one.1 h

variable [Finite G] [Algebra.IsInvariant R S G]

private theorem arithFrobAt_smul (τ : G) (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] [Finite (S ⧸ τ • Q)] (hI : Q.inertia G = ⊥) :
    arithFrobAt R G (τ • Q) = τ * arithFrobAt R G Q * τ⁻¹ := by
  have h1 : IsArithFrobAt R (arithFrobAt R G (τ • Q)) (τ • Q) := IsArithFrobAt.arithFrobAt R G (τ • Q)
  have h2 : IsArithFrobAt R (τ * arithFrobAt R G Q * τ⁻¹) (τ • Q) := (IsArithFrobAt.arithFrobAt R G Q).conj τ
  have h3 := h1.mul_inv_mem_inertia h2
  rw [inertia_smul_eq_bot τ Q hI, Subgroup.mem_bot] at h3
  exact mul_inv_eq_one.1 h3

end Transport

section Artin

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  (v : HeightOneSpectrum (𝓞 K))

private theorem arithFrobAt_eq_artinFrob [IsMulCommutative (M ≃ₐ[K] M)] (Q : Ideal (𝓞 M)) [Q.IsPrime] [Finite (𝓞 M ⧸ Q)]
    (hQ : Q.under (𝓞 K) = v.asIdeal) (hI : Q.inertia (M ≃ₐ[K] M) = ⊥) :
    arithFrobAt (𝓞 K) (M ≃ₐ[K] M) Q = artinFrob K M v := by
  haveI : Q.LiesOver v.asIdeal := ⟨hQ.symm⟩
  haveI := v.isMaximal
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal (primeAbove K M v) Q (M ≃ₐ[K] M)
  subst hτ
  have hI₀ : (primeAbove K M v).inertia (M ≃ₐ[K] M) = ⊥ := by
    have h := inertia_smul_eq_bot τ⁻¹ (τ • primeAbove K M v) hI
    rwa [inv_smul_smul] at h
  rw [arithFrobAt_smul τ (primeAbove K M v) hI₀, IsMulCommutative.is_comm.comm τ, mul_inv_cancel_right]
  rfl

private theorem eq_artinFrob_of_isArithFrobAt [IsMulCommutative (M ≃ₐ[K] M)] {σ : M ≃ₐ[K] M} {Q : Ideal (𝓞 M)} [Q.IsPrime]
    (H : IsArithFrobAt (𝓞 K) σ Q) (hQ : Q.under (𝓞 K) = v.asIdeal) (hI : Q.inertia (M ≃ₐ[K] M) = ⊥) : σ = artinFrob K M v := by
  haveI := finite_quotient_of_under_eq K M v hQ
  rw [← arithFrobAt_eq_artinFrob K M v Q hQ hI]
  exact eq_of_isArithFrobAt_of_inertia_eq_bot H (IsArithFrobAt.arithFrobAt (𝓞 K) (M ≃ₐ[K] M) Q) hI

end Artin

section Restrict

variable (K M M' : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Field M'] [NumberField M']
  [Algebra K M] [Algebra K M'] [Algebra M M'] [IsScalarTower K M M'] [IsGalois K M] [IsGalois K M']

private scoped instance : IsScalarTower (𝓞 K) (𝓞 M) (𝓞 M') :=
  IsScalarTower.of_algebraMap_eq fun x => by
    refine RingOfIntegers.ext ?_
    show algebraMap K M' (x : K) = algebraMap M M' (algebraMap (𝓞 K) (𝓞 M) x : M)
    rw [show (algebraMap (𝓞 K) (𝓞 M) x : M) = algebraMap K M (x : K) from rfl, ← IsScalarTower.algebraMap_apply K M M']

private theorem isArithFrobAt_restrictNormal (τ : M' ≃ₐ[K] M') (Q' : Ideal (𝓞 M')) (H : IsArithFrobAt (𝓞 K) τ Q') :
    IsArithFrobAt (𝓞 K) (AlgEquiv.restrictNormalHom M τ) (Q'.under (𝓞 M)) := by
  intro x
  have hcard : Nat.card (𝓞 K ⧸ (Q'.under (𝓞 M)).under (𝓞 K)) = Nat.card (𝓞 K ⧸ Q'.under (𝓞 K)) := by
    rw [Ideal.under_under]
  have hkey : algebraMap (𝓞 M) (𝓞 M') ((AlgEquiv.restrictNormalHom M τ) • x) = τ • algebraMap (𝓞 M) (𝓞 M') x := by
    refine RingOfIntegers.ext ?_
    show algebraMap M M' ((τ.restrictNormal M) (x : M)) = τ (algebraMap M M' (x : M))
    exact AlgEquiv.restrictNormal_commutes τ M (x : M)
  rw [hcard, Ideal.under_def, Ideal.mem_comap, map_sub, map_pow]
  erw [hkey]
  exact H (algebraMap (𝓞 M) (𝓞 M') x)

private theorem restrictNormal_artinFrob [IsMulCommutative (M ≃ₐ[K] M)] (v : HeightOneSpectrum (𝓞 K))
    (hI : ((primeAbove K M' v).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥) :
    AlgEquiv.restrictNormalHom M (artinFrob K M' v) = artinFrob K M v := by
  have H := isArithFrobAt_restrictNormal K M M' (artinFrob K M' v) (primeAbove K M' v) (isArithFrobAt_artinFrob K M' v)
  haveI : ((primeAbove K M' v).under (𝓞 M)).IsPrime := Ideal.IsPrime.under (𝓞 M) (primeAbove K M' v)
  refine eq_artinFrob_of_isArithFrobAt K M v H ?_ hI
  rw [Ideal.under_under, under_primeAbove]

end Restrict

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

open NumberField IsDedekindDomain

section Symbol

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.Deep.NTSupply"

open scoped nonZeroDivisors

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  [IsMulCommutative (M ≃ₐ[K] M)]

open scoped IsMulCommutative

omit [NumberField M] [Algebra K M] [IsGalois K M] [IsMulCommutative (M ≃ₐ[K] M)] in

private theorem map_raySymbol {N N' : Type*} [CommGroup N] [CommGroup N'] (φ : N →* N') (f : HeightOneSpectrum (𝓞 K) → N)
    (I : FractionalIdeal ((𝓞 K)⁰) K) : φ (raySymbol K f I) = raySymbol K (φ ∘ f) I := by
  unfold raySymbol
  rw [φ.map_finprod (hasFiniteMulSupport_raySymbol_factors K f I)]
  simp only [map_zpow, Function.comp_apply]

variable (M' : Type*) [Field M'] [NumberField M'] [Algebra K M'] [Algebra M M'] [IsScalarTower K M M'] [IsGalois K M']
  [IsMulCommutative (M' ≃ₐ[K] M')]

private theorem restrictNormalHom_artinSymbol (𝔣 : Ideal (𝓞 K))
    (hI : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 → ((primeAbove K M' v).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥)
    (I : ↥(coprimeToModulus K 𝔣)) :
    AlgEquiv.restrictNormalHom M (artinSymbol K M' 𝔣 I) = artinSymbol K M 𝔣 I := by
  rw [artinSymbol, artinSymbol, raySymbolHom_apply, raySymbolHom_apply, map_raySymbol]
  unfold raySymbol
  refine finprod_congr fun v => ?_
  by_cases hv : v.asIdeal ∣ 𝔣
  · rw [I.2 v hv, zpow_zero, zpow_zero]
  · rw [Function.comp_apply, restrictNormal_artinFrob K M M' v (hI v hv)]

end Symbol
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.Deep.NTSupply"

open scoped IsMulCommutative nonZeroDivisors

section Finite

variable (K E : Type*) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

private scoped instance moduleFinite_ringOfIntegers : Module.Finite (𝓞 K) (𝓞 E) :=
  Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 E)

end Finite
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin"

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.Deep.NTSupply NumberField IsDedekindDomain"

open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff relNormCTM"
p2m_open "HeckeCharacter"

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private theorem fracRelNormUnit_primeUnit (w : HeightOneSpectrum (𝓞 E))
    (𝔭 : HeightOneSpectrum (𝓞 k)) (h𝔭w : w.asIdeal.under (𝓞 k) = 𝔭.asIdeal) :
    fracRelNormUnit k E (primeUnit E w)
      = primeUnit k 𝔭 ^ (𝔭.asIdeal.inertiaDeg' w.asIdeal) := by
  have heq : placeUnder' k E w = 𝔭 :=
    IsDedekindDomain.HeightOneSpectrum.ext (by rw [placeUnder'_asIdeal, h𝔭w])
  show raySymbolUnitsHom E _ (primeUnit E w) = _
  rw [show raySymbolUnitsHom E _ (primeUnit E w)
        = raySymbol E _ ((primeUnit E w : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) :
            FractionalIdeal ((𝓞 E)⁰) E) from rfl,
    raySymbol_primeUnit, heq]

private theorem relNorm_mem_nzd {I : Ideal (𝓞 E)} (hI : I ∈ (nonZeroDivisors (Ideal (𝓞 E)))) :
    Ideal.relNorm (𝓞 k) I ∈ nonZeroDivisors (Ideal (𝓞 k)) :=
  mem_nonZeroDivisors_of_ne_zero (fun h =>
    (mem_nonZeroDivisors_iff_ne_zero.mp hI) (by
      rw [Submodule.zero_eq_bot] at *; exact Ideal.relNorm_eq_bot_iff.mp h))

private theorem fracRelNormUnit_primeUnit_eq_relNorm (w : HeightOneSpectrum (𝓞 E)) :
    fracRelNormUnit k E (primeUnit E w)
      = FractionalIdeal.mk0 k ⟨Ideal.relNorm (𝓞 k) w.asIdeal, relNorm_mem_nzd k E
          (mem_nonZeroDivisors_of_ne_zero (by
            rw [Ne, Submodule.zero_eq_bot]; exact w.ne_bot))⟩ := by
  haveI : PerfectField (FractionRing (𝓞 k)) := PerfectField.ofCharZero
  haveI : w.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal w.isPrime w.ne_bot
  haveI : (placeUnder' k E w).asIdeal.IsMaximal :=
    Ideal.IsPrime.isMaximal (placeUnder' k E w).isPrime (placeUnder' k E w).ne_bot
  haveI : w.asIdeal.LiesOver (placeUnder' k E w).asIdeal :=
    ⟨(placeUnder'_asIdeal k E w).symm⟩
  rw [fracRelNormUnit_primeUnit k E w (placeUnder' k E w) (placeUnder'_asIdeal k E w).symm]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, primeUnit_val, FractionalIdeal.coe_mk0,
    ← FractionalIdeal.coeIdeal_pow]
  rw [Ideal.inertiaDeg'_eq_inertiaDeg]
  exact congrArg _
    (Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (placeUnder' k E w).asIdeal).symm

private theorem fracRelNormUnit_mk0 (I : (Ideal (𝓞 E))⁰) :
    ((fracRelNormUnit k E (FractionalIdeal.mk0 E I) :
        (FractionalIdeal ((𝓞 k)⁰) k)ˣ) : FractionalIdeal ((𝓞 k)⁰) k)
      = ((Ideal.relNorm (𝓞 k) (I : Ideal (𝓞 E)) : Ideal (𝓞 k)) :
          FractionalIdeal ((𝓞 k)⁰) k) := by
  obtain ⟨J, hJ⟩ := I
  have hJ' : J ≠ ⊥ := fun h =>
    (mem_nonZeroDivisors_iff_ne_zero.mp hJ) (h.trans (Submodule.zero_eq_bot (R := 𝓞 E)).symm)
  simp only at *
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hJ'
  | h₂ u hu =>
    obtain rfl : u = ⊤ := Ideal.isUnit_iff.mp hu
    rw [show FractionalIdeal.mk0 E (⟨(⊤ : Ideal (𝓞 E)), hJ⟩ : (Ideal (𝓞 E))⁰) = 1 from
        Units.ext (by rw [FractionalIdeal.coe_mk0, Units.val_one, FractionalIdeal.coeIdeal_top]),
      map_one, Units.val_one, ← Ideal.one_eq_top, map_one, Ideal.one_eq_top,
      FractionalIdeal.coeIdeal_top]
  | h₃ a p ha hp ih =>
    have ha' : a ≠ ⊥ := fun h => ha (h.trans (Submodule.zero_eq_bot (R := 𝓞 E)).symm)
    have hp_nz : p ∈ nonZeroDivisors (Ideal (𝓞 E)) :=
      mem_nonZeroDivisors_of_ne_zero
        (fun h => hp.ne_zero (h.trans (Submodule.zero_eq_bot (R := 𝓞 E)).symm))
    have ha_nz : a ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero ha
    let w : HeightOneSpectrum (𝓞 E) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    have hpw : (FractionalIdeal.mk0 E ⟨p, hp_nz⟩ : (FractionalIdeal ((𝓞 E)⁰) E)ˣ)
        = primeUnit E w := by
      unfold primeUnit; exact congrArg (FractionalIdeal.mk0 E) (Subtype.ext rfl)
    rw [show (⟨p * a, hJ⟩ : (Ideal (𝓞 E))⁰) = ⟨p, hp_nz⟩ * ⟨a, ha_nz⟩ from rfl,
      map_mul, map_mul (fracRelNormUnit k E), Units.val_mul, hpw,
      fracRelNormUnit_primeUnit_eq_relNorm k E w, FractionalIdeal.coe_mk0,
      ih ha_nz ha', map_mul (Ideal.relNorm (𝓞 k)), FractionalIdeal.coeIdeal_mul]

private theorem fracRelNormUnit_principalUnit (α : 𝓞 E) (hα : α ≠ 0) :
    ((fracRelNormUnit k E (principalUnit E α hα) :
        (FractionalIdeal ((𝓞 k)⁰) k)ˣ) : FractionalIdeal ((𝓞 k)⁰) k)
      = ((Ideal.span {Algebra.intNorm (𝓞 k) (𝓞 E) α} : Ideal (𝓞 k)) :
          FractionalIdeal ((𝓞 k)⁰) k) := by
  rw [show principalUnit E α hα = FractionalIdeal.mk0 E ⟨Ideal.span {α}, _⟩ from rfl,
    fracRelNormUnit_mk0 k E, Ideal.relNorm_singleton]

end HeckeCharacter
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

set_option maxHeartbeats 3200000

noncomputable section

namespace M4aP2

p2m_open "NumberField nonZeroDivisors IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.Deep.NTSupply"

variable (K : Type*) [Field K] [NumberField K] (q : ℕ)

private theorem norm_int_cast_eq_one_of_sub_one_mem {α : 𝓞 K}
    (hα : α - 1 ∈ Ideal.span {(q : 𝓞 K)}) :
    ((Algebra.norm ℤ α : ℤ) : ZMod q) = 1 := by
  classical
  obtain ⟨γ, hγ⟩ := Ideal.mem_span_singleton'.mp hα
  have hsm : q • γ = γ * (q : 𝓞 K) := by rw [nsmul_eq_mul, mul_comm]
  have hαeq : α = 1 + q • γ := by rw [hsm, hγ]; ring
  let b := RingOfIntegers.basis K
  have h1 : ((Algebra.norm ℤ α : ℤ) : ZMod q)
      = ((Int.castRingHom (ZMod q)).mapMatrix (Algebra.leftMulMatrix b α)).det := by
    rw [Algebra.norm_eq_matrix_det b, ← RingHom.map_det]; rfl
  have h0 : (q • (Int.castRingHom (ZMod q)).mapMatrix (Algebra.leftMulMatrix b γ)
      : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 K))
        (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) (ZMod q)) = 0 := by
    ext i j
    simp [Matrix.smul_apply, nsmul_eq_mul]
  rw [h1, hαeq, map_add, map_one, map_nsmul, map_add, map_one, map_nsmul, h0, add_zero,
    Matrix.det_one]

private theorem norm_int_pos_of_totPos {α : 𝓞 K} (h0 : α ≠ 0)
    (hpos : ∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) :
    0 < Algebra.norm ℤ α := by
  classical
  set x : K := algebraMap (𝓞 K) K α with hxdef
  have hx0 : x ≠ 0 := by
    rw [hxdef, map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
    exact h0

  have hper : ∀ w : InfinitePlace K, ∃ r : ℝ, 0 < r ∧
      (∏ φ ∈ ({φ | InfinitePlace.mk φ = w} : Finset (K →+* ℂ)), φ x) = (r : ℂ) := by
    intro w
    have hfibset : ({φ | InfinitePlace.mk φ = w} : Finset (K →+* ℂ))
        = {w.embedding, NumberField.ComplexEmbedding.conjugate w.embedding} := by
      ext φ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro h
        have h' : InfinitePlace.mk φ = InfinitePlace.mk w.embedding :=
          h.trans (InfinitePlace.mk_embedding w).symm
        rcases InfinitePlace.mk_eq_iff.mp h' with h1 | h2
        · exact Or.inl h1
        · exact Or.inr ((star_star φ).symm.trans (congrArg star h2))
      · rintro (h | h)
        · rw [h, InfinitePlace.mk_embedding]
        · rw [h, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
    by_cases hw : InfinitePlace.IsReal w
    · have hre : NumberField.ComplexEmbedding.conjugate w.embedding = w.embedding :=
        NumberField.ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hw)
      refine ⟨(InfinitePlace.embedding_of_isReal hw) x, hpos _, ?_⟩
      rw [hfibset, hre, Finset.insert_eq_self.mpr (Finset.mem_singleton_self _),
        Finset.prod_singleton, InfinitePlace.embedding_of_isReal_apply hw]
    · have hne : w.embedding ≠ NumberField.ComplexEmbedding.conjugate w.embedding := by
        intro h
        exact hw (InfinitePlace.isReal_iff.mpr
          (NumberField.ComplexEmbedding.isReal_iff.mpr h.symm))
      have hval0 : w.embedding x ≠ 0 := by
        rw [← map_zero w.embedding]
        exact fun h => hx0 (w.embedding.injective h)
      refine ⟨Complex.normSq (w.embedding x), Complex.normSq_pos.mpr hval0, ?_⟩
      rw [hfibset, Finset.prod_pair hne,
        NumberField.ComplexEmbedding.conjugate_coe_eq, Complex.mul_conj]
  choose r hrpos hreq using hper

  have htot : algebraMap ℚ ℂ (Algebra.norm ℚ x) = ((∏ w : InfinitePlace K, r w : ℝ) : ℂ) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ x,
      ← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ : K →+* ℂ => φ x)
        (fun σ : K →ₐ[ℚ] ℂ => σ x)
        (fun φ => by simp [RingHom.equivRatAlgHom_apply]),
      ← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ : K →+* ℂ => φ x),
      Finset.prod_congr rfl fun w _ => hreq w, ← Complex.ofReal_prod]

  have hofreal : (((Algebra.norm ℚ x : ℚ) : ℝ) : ℂ) = ((∏ w : InfinitePlace K, r w : ℝ) : ℂ) := by
    rw [← htot, eq_ratCast (algebraMap ℚ ℂ) (Algebra.norm ℚ x), Complex.ofReal_ratCast]
  have hQpos : 0 < Algebra.norm ℚ x := by
    have hreal : ((Algebra.norm ℚ x : ℚ) : ℝ) = ∏ w : InfinitePlace K, r w :=
      Complex.ofReal_inj.mp hofreal
    have hP : 0 < ∏ w : InfinitePlace K, r w :=
      Finset.prod_pos fun w _ => hrpos w
    rw [← Rat.cast_pos (K := ℝ), hreal]
    exact hP

  have hcoe : ((Algebra.norm ℤ α : ℤ) : ℚ) = Algebra.norm ℚ x := Algebra.coe_norm_int α
  have : (0 : ℚ) < ((Algebra.norm ℤ α : ℤ) : ℚ) := by rw [hcoe]; exact hQpos
  exact_mod_cast this

private theorem absNorm_coprime_of_not_dvd (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ v.asIdeal ∣ Ideal.span {(q : 𝓞 K)}) :
    Nat.Coprime (Ideal.absNorm v.asIdeal) q := by
  classical
  haveI hmax : v.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal v.isPrime v.ne_bot
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  haveI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  obtain ⟨n, hp, hcard⟩ :=
    FiniteField.card (𝓞 K ⧸ v.asIdeal) (ringChar (𝓞 K ⧸ v.asIdeal))
  have habs : Ideal.absNorm v.asIdeal = ringChar (𝓞 K ⧸ v.asIdeal) ^ (n : ℕ) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, ← hcard]
  rw [habs]
  refine Nat.Coprime.pow_left _ ?_
  by_contra hnc
  have hpq : ringChar (𝓞 K ⧸ v.asIdeal) ∣ q := by
    by_contra hdvd
    exact hnc ((Nat.Prime.coprime_iff_not_dvd hp).mpr hdvd)
  apply hv
  rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
  have hpmem : ((ringChar (𝓞 K ⧸ v.asIdeal) : ℕ) : 𝓞 K) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [map_natCast (Ideal.Quotient.mk v.asIdeal), CharP.cast_eq_zero]
  obtain ⟨t, ht⟩ := hpq
  have hqt : ((q : ℕ) : 𝓞 K)
      = ((ringChar (𝓞 K ⧸ v.asIdeal) : ℕ) : 𝓞 K) * ((t : ℕ) : 𝓞 K) := by
    rw [← Nat.cast_mul, ← ht]
  rw [SetLike.mem_coe, hqt]
  exact Ideal.mul_mem_right _ _ hpmem

private def normClass (v : HeightOneSpectrum (𝓞 K)) : (ZMod q)ˣ :=
  if h : Nat.Coprime (Ideal.absNorm v.asIdeal) q then ZMod.unitOfCoprime _ h else 1

private theorem normClass_coe (v : HeightOneSpectrum (𝓞 K))
    (h : Nat.Coprime (Ideal.absNorm v.asIdeal) q) :
    ((normClass K q v : (ZMod q)ˣ) : ZMod q) = (Ideal.absNorm v.asIdeal : ZMod q) := by
  rw [normClass, dif_pos h, ZMod.coe_unitOfCoprime]

private theorem raySymbol_normClass_coe {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (hcop : I ⊔ Ideal.span {(q : 𝓞 K)} = ⊤) :
    ((raySymbol K (normClass K q) (I : FractionalIdeal ((𝓞 K)⁰) K) : (ZMod q)ˣ) : ZMod q)
      = (Ideal.absNorm I : ZMod q) := by
  classical
  have hI0 : I ≠ 0 := by simpa using hI
  have hvcop : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ I →
      Nat.Coprime (Ideal.absNorm v.asIdeal) q := by
    intro v hvI
    refine absNorm_coprime_of_not_dvd K q v fun hdvd => ?_
    have h1 : I ≤ v.asIdeal := Ideal.le_of_dvd hvI
    have h2 : Ideal.span {(q : 𝓞 K)} ≤ v.asIdeal := Ideal.le_of_dvd hdvd
    have htop : (⊤ : Ideal (𝓞 K)) ≤ v.asIdeal := hcop ▸ sup_le h1 h2
    exact v.isPrime.ne_top (top_le_iff.mp htop)
  have hdvd_of_n : ∀ v : HeightOneSpectrum (𝓞 K),
      (Associates.mk v.asIdeal).count (Associates.mk I).factors ≠ 0 → v.asIdeal ∣ I := by
    intro v hv
    rwa [← Associates.count_ne_zero_iff_dvd hI0 v.irreducible]
  have hfuneq : (fun v : HeightOneSpectrum (𝓞 K) =>
        normClass K q v ^ FractionalIdeal.count K v (I : FractionalIdeal ((𝓞 K)⁰) K))
      = fun v => normClass K q v
          ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
    funext v
    rw [FractionalIdeal.count_coe K v hI0, zpow_natCast]
  have hfin := hasFiniteMulSupport_raySymbol_factors K (normClass K q)
    (I : FractionalIdeal ((𝓞 K)⁰) K)
  rw [hfuneq] at hfin
  have hsym : raySymbol K (normClass K q) (I : FractionalIdeal ((𝓞 K)⁰) K)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          normClass K q v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
    rw [raySymbol, hfuneq]
  have hcoe : ((∏ᶠ v : HeightOneSpectrum (𝓞 K),
        normClass K q v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors
          : (ZMod q)ˣ) : ZMod q)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          ((normClass K q v : ZMod q))
            ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
    rw [show ((∏ᶠ v : HeightOneSpectrum (𝓞 K),
          normClass K q v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors
            : (ZMod q)ˣ) : ZMod q)
        = Units.coeHom (ZMod q) (∏ᶠ v : HeightOneSpectrum (𝓞 K),
            normClass K q v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors)
        from rfl,
      MonoidHom.map_finprod (Units.coeHom (ZMod q)) hfin]
    exact finprod_congr fun v => by
      rw [Units.coeHom_apply, Units.val_pow_eq_pow_val]
  have hval : (fun v : HeightOneSpectrum (𝓞 K) =>
        ((normClass K q v : ZMod q))
          ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors)
      = fun v => ((Ideal.absNorm v.asIdeal : ZMod q))
          ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
    funext v
    by_cases hv : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0
    · rw [hv, pow_zero, pow_zero]
    · rw [normClass_coe K q v (hvcop v (hdvd_of_n v hv))]
  have hnfin : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 K) => Ideal.absNorm v.asIdeal
        ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors) := by
    show (Function.mulSupport _).Finite
    refine ((Filter.eventually_cofinite.mp
      (FractionalIdeal.finite_factors (I : FractionalIdeal ((𝓞 K)⁰) K))).subset ?_)
    intro v hv
    rw [Function.mem_mulSupport] at hv
    simp only [Set.mem_setOf_eq]
    intro hcount
    apply hv
    rw [FractionalIdeal.count_coe K v hI0, Nat.cast_eq_zero] at hcount
    show Ideal.absNorm v.asIdeal
      ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors = 1
    rw [hcount, pow_zero]
  have hmfin : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 K) => v.maxPowDividing I) := by
    show (Function.mulSupport _).Finite
    refine ((Filter.eventually_cofinite.mp
      (FractionalIdeal.finite_factors (I : FractionalIdeal ((𝓞 K)⁰) K))).subset ?_)
    intro v hv
    rw [Function.mem_mulSupport] at hv
    simp only [Set.mem_setOf_eq]
    intro hcount
    apply hv
    rw [FractionalIdeal.count_coe K v hI0, Nat.cast_eq_zero] at hcount
    show v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors = 1
    rw [hcount, pow_zero]
  have hcast : ((∏ᶠ v : HeightOneSpectrum (𝓞 K), Ideal.absNorm v.asIdeal
        ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors : ℕ) : ZMod q)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm v.asIdeal : ZMod q))
          ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
    rw [show ((∏ᶠ v : HeightOneSpectrum (𝓞 K), Ideal.absNorm v.asIdeal
          ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors : ℕ) : ZMod q)
        = (Nat.castRingHom (ZMod q)) (∏ᶠ v : HeightOneSpectrum (𝓞 K),
            Ideal.absNorm v.asIdeal
              ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors)
        from rfl,
      map_finprod (Nat.castRingHom (ZMod q)) hnfin]
    exact finprod_congr fun v => by rw [map_pow]; rfl
  have hnat : (∏ᶠ v : HeightOneSpectrum (𝓞 K), Ideal.absNorm v.asIdeal
        ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors)
      = Ideal.absNorm I := by
    conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI0]
    rw [map_finprod Ideal.absNorm hmfin]
    refine finprod_congr fun v => ?_
    show Ideal.absNorm v.asIdeal
        ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors
      = Ideal.absNorm (v.asIdeal
          ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors)
    exact (map_pow Ideal.absNorm _ _).symm
  rw [hsym, hcoe, hval, ← hcast, hnat]

private theorem normClassKillsRay {𝔣 : Ideal (𝓞 K)} (hq𝔣 : Ideal.span {(q : 𝓞 K)} ∣ 𝔣) :
    ∀ α : 𝓞 K, α ≠ 0 → α - 1 ∈ 𝔣 →
      (∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) →
      raySymbol K (normClass K q)
        ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) = 1 := by
  intro α hα0 hα1 hpos
  have hspan : (Ideal.span {α} : Ideal (𝓞 K)) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hα0
  have hα1q : α - 1 ∈ Ideal.span {(q : 𝓞 K)} := Ideal.le_of_dvd hq𝔣 hα1
  have hcop : (Ideal.span {α} : Ideal (𝓞 K)) ⊔ Ideal.span {(q : 𝓞 K)} = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : α - (α - 1) = 1 := by ring
    exact h1 ▸ Submodule.sub_mem _
      (Ideal.mem_sup_left (Ideal.subset_span rfl))
      (Ideal.mem_sup_right hα1q)
  have h1 := raySymbol_normClass_coe K q hspan hcop
  rw [Ideal.absNorm_span_singleton] at h1
  have hpos' : 0 < Algebra.norm ℤ α := norm_int_pos_of_totPos K hα0 hpos
  have hnat : (((Algebra.norm ℤ α).natAbs : ℕ) : ZMod q) = 1 := by
    rw [← Int.cast_natCast (R := ZMod q), Int.natAbs_of_nonneg hpos'.le,
      norm_int_cast_eq_one_of_sub_one_mem K q hα1q]
  rw [hnat] at h1
  exact Units.val_eq_one.mp h1

end M4aP2
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin"

section

open NumberField

namespace M4aP2

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private theorem prod_sub_one_mem {R : Type*} [CommRing R] (J : Ideal R)
    {ι : Type*} (s : Finset ι) (f : ι → R) (h : ∀ i ∈ s, f i - 1 ∈ J) :
    (∏ i ∈ s, f i) - 1 ∈ J := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons]
    have h1 := h a (Finset.mem_cons_self a s)
    have h2 := ih fun i hi => h i (Finset.mem_cons_of_mem hi)
    have hsplit : f a * ∏ i ∈ s, f i - 1 = f a * ((∏ i ∈ s, f i) - 1) + (f a - 1) := by ring
    rw [hsplit]
    exact J.add_mem (Ideal.mul_mem_left _ _ h2) h1

private abbrev NCl := ↥(IntermediateField.normalClosure k E (AlgebraicClosure k))

@[reducible] private noncomputable def algONcl : Algebra (𝓞 k) (𝓞 (NCl k E)) :=
  (RingOfIntegers.mapRingHom (algebraMap k (NCl k E))).toAlgebra

attribute [local instance] algONcl

omit [NumberField k] [NumberField E] in
private theorem algONcl_coe (x : 𝓞 k) :
    (algebraMap (𝓞 k) (𝓞 (NCl k E)) x : NCl k E) = algebraMap k (NCl k E) (x : k) := rfl

omit [NumberField k] [NumberField E] in
private theorem algONcl_injective :
    Function.Injective (algebraMap (𝓞 k) (𝓞 (NCl k E))) := by
  intro a b h
  have h1 : algebraMap k (NCl k E) (a : k) = algebraMap k (NCl k E) (b : k) := by
    rw [← algONcl_coe, ← algONcl_coe, h]
  exact FaithfulSMul.algebraMap_injective (𝓞 k) k ((algebraMap k (NCl k E)).injective h1)

private scoped instance : IsScalarTower ℤ (𝓞 k) (𝓞 (NCl k E)) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

private scoped instance : Algebra.IsIntegral (𝓞 k) (𝓞 (NCl k E)) :=
  ⟨fun x => IsIntegral.tower_top (R := ℤ) (Algebra.IsIntegral.isIntegral x)⟩

private scoped instance : FaithfulSMul (𝓞 k) (𝓞 (NCl k E)) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (algONcl_injective k E)

variable {k E}

private noncomputable def embO (σ : E →ₐ[k] AlgebraicClosure k) :
    𝓞 E →+* 𝓞 (NCl k E) :=
  RingOfIntegers.mapRingHom
    ((σ.codRestrict _ fun x => σ.fieldRange_le_normalClosure ⟨x, rfl⟩ :
      E →ₐ[k] NCl k E) : E →+* NCl k E)

omit [NumberField k] [NumberField E] in
private theorem embO_coe (σ : E →ₐ[k] AlgebraicClosure k) (x : 𝓞 E) :
    algebraMap (NCl k E) (AlgebraicClosure k) ((embO σ x : 𝓞 (NCl k E)) : NCl k E)
    = σ (algebraMap (𝓞 E) E x) := rfl

omit [NumberField k] [NumberField E] in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem embO_comp (σ : E →ₐ[k] AlgebraicClosure k) :
    (embO σ).comp (algebraMap (𝓞 k) (𝓞 E)) = algebraMap (𝓞 k) (𝓞 (NCl k E)) := by
  apply RingHom.ext
  intro x
  apply FaithfulSMul.algebraMap_injective (𝓞 (NCl k E)) (NCl k E)
  show (σ.codRestrict _ fun z => σ.fieldRange_le_normalClosure ⟨z, rfl⟩ :
      E →ₐ[k] NCl k E) (algebraMap k E (x : k))
    = algebraMap k (NCl k E) (x : k)
  exact (σ.codRestrict _ fun z => σ.fieldRange_le_normalClosure ⟨z, rfl⟩ :
    E →ₐ[k] NCl k E).commutes (x : k)

variable (k E)

set_option synthInstance.maxHeartbeats 1600000 in

private theorem intNorm_sub_one_mem_of_sub_one_mem (𝔠 : Ideal (𝓞 k)) (y : 𝓞 E)
    (hy : y - 1 ∈ 𝔠.map (algebraMap (𝓞 k) (𝓞 E))) :
    Algebra.intNorm (𝓞 k) (𝓞 E) y - 1 ∈ 𝔠 := by
  classical
  haveI : FiniteDimensional k E := FiniteDimensional.right ℚ k E

  have hmem : ∀ σ : E →ₐ[k] AlgebraicClosure k,
      embO σ y - 1 ∈ 𝔠.map (algebraMap (𝓞 k) (𝓞 (NCl k E))) := by
    intro σ
    have h1 : embO σ (y - 1) ∈ (𝔠.map (algebraMap (𝓞 k) (𝓞 E))).map (embO σ) :=
      Ideal.mem_map_of_mem (embO σ) hy
    rw [Ideal.map_map, embO_comp σ] at h1
    simpa [map_sub] using h1
  have hPsub : (∏ σ : E →ₐ[k] AlgebraicClosure k, embO σ y) - 1
      ∈ 𝔠.map (algebraMap (𝓞 k) (𝓞 (NCl k E))) :=
    prod_sub_one_mem _ _ _ fun σ _ => hmem σ

  have hPeq : (∏ σ : E →ₐ[k] AlgebraicClosure k, embO σ y)
      = algebraMap (𝓞 k) (𝓞 (NCl k E)) (Algebra.intNorm (𝓞 k) (𝓞 E) y) := by
    apply FaithfulSMul.algebraMap_injective (𝓞 (NCl k E)) (NCl k E)
    apply RingHom.injective (algebraMap (NCl k E) (AlgebraicClosure k))
    rw [show ((algebraMap (𝓞 (NCl k E)) (NCl k E))
        (∏ σ : E →ₐ[k] AlgebraicClosure k, embO σ y))
        = ∏ σ : E →ₐ[k] AlgebraicClosure k,
          ((embO σ y : 𝓞 (NCl k E)) : NCl k E) from map_prod _ _ _,
      map_prod]
    have hL : ∀ σ : E →ₐ[k] AlgebraicClosure k,
        algebraMap (NCl k E) (AlgebraicClosure k) ((embO σ y : 𝓞 (NCl k E)) : NCl k E)
        = σ (algebraMap (𝓞 E) E y) := fun σ => embO_coe σ y
    rw [Finset.prod_congr rfl fun σ _ => hL σ]
    have hR : algebraMap (NCl k E) (AlgebraicClosure k)
        ((algebraMap (𝓞 k) (𝓞 (NCl k E)) (Algebra.intNorm (𝓞 k) (𝓞 E) y) : NCl k E))
        = algebraMap k (AlgebraicClosure k)
          (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y)) := by
      rw [algONcl_coe]
      exact (IsScalarTower.algebraMap_apply k (NCl k E) (AlgebraicClosure k) _).symm
    rw [hR, Algebra.algebraMap_intNorm (A := 𝓞 k) (B := 𝓞 E) (K := k) (L := E)]
    exact (Algebra.norm_eq_prod_embeddings (K := k) (L := E)
      (E := AlgebraicClosure k) _).symm

  have hfin : algebraMap (𝓞 k) (𝓞 (NCl k E)) (Algebra.intNorm (𝓞 k) (𝓞 E) y - 1)
      ∈ 𝔠.map (algebraMap (𝓞 k) (𝓞 (NCl k E))) := by
    rw [map_sub, map_one, ← hPeq]
    exact hPsub
  haveI hTF : Module.IsTorsionFree (𝓞 k) (𝓞 (NCl k E)) := inferInstance
  haveI hFlat : Module.Flat (𝓞 k) (𝓞 (NCl k E)) := inferInstance
  haveI hFF : Module.FaithfullyFlat (𝓞 k) (𝓞 (NCl k E)) := inferInstance
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat
    (A := 𝓞 k) (B := 𝓞 (NCl k E)) 𝔠]
  exact Ideal.mem_comap.mpr hfin

private theorem intNorm_totPos_of_totPos (y : 𝓞 E) (hy0 : y ≠ 0)
    (hpos : ∀ τ : E →+* ℝ, 0 < τ (algebraMap (𝓞 E) E y)) :
    ∀ τ' : k →+* ℝ, 0 < τ' (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y)) := by
  intro τ'
  classical
  letI : Algebra k ℂ := (Complex.ofRealHom.comp τ').toAlgebra
  haveI : FiniteDimensional k E := FiniteDimensional.right ℚ k E
  set yE : E := algebraMap (𝓞 E) E y with hyEdef
  have hyE0 : yE ≠ 0 := fun h =>
    hy0 ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).mp h)
  have hσ0 : ∀ σ : E →ₐ[k] ℂ, σ yE ≠ 0 := fun σ h =>
    hyE0 ((map_eq_zero_iff _ (RingHom.injective (σ : E →+* ℂ))).mp h)
  have hstar_alg : ∀ c : k, (starRingEnd ℂ) (algebraMap k ℂ c) = algebraMap k ℂ c := fun c =>
    Complex.conj_ofReal _
  let conjA : (E →ₐ[k] ℂ) → (E →ₐ[k] ℂ) := fun σ =>
    { toRingHom := (starRingEnd ℂ).comp (σ : E →+* ℂ)
      commutes' := fun c => by
        show (starRingEnd ℂ) (σ (algebraMap k E c)) = algebraMap k ℂ c
        rw [σ.commutes]
        exact hstar_alg c }
  have hconjA_apply : ∀ (σ : E →ₐ[k] ℂ) (x : E), conjA σ x = (starRingEnd ℂ) (σ x) :=
    fun _ _ => rfl
  have hconjA_invol : ∀ σ, conjA (conjA σ) = σ := fun σ => AlgHom.ext fun x =>
    Complex.conj_conj (σ x)
  have hf_pair : ∀ σ : E →ₐ[k] ℂ,
      σ yE / (‖σ yE‖ : ℂ) * ((conjA σ) yE / (‖(conjA σ) yE‖ : ℂ)) = 1 := by
    intro σ
    have hz : σ yE ≠ 0 := hσ0 σ
    have hr0 : (‖σ yE‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    have hc : (conjA σ) yE = (starRingEnd ℂ) (σ yE) := rfl
    rw [hc, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj', ← sq]
    exact div_self (pow_ne_zero 2 hr0)
  have hf_fixed : ∀ σ : E →ₐ[k] ℂ, σ yE / (‖σ yE‖ : ℂ) ≠ 1 → conjA σ ≠ σ := by
    intro σ hf1 heq
    apply hf1
    have hreal : NumberField.ComplexEmbedding.IsReal (σ : E →+* ℂ) := by
      rw [NumberField.ComplexEmbedding.isReal_iff]
      ext x
      have h1 := congrArg (fun ψ : E →ₐ[k] ℂ => ψ x) heq
      simpa [NumberField.ComplexEmbedding.conjugate_coe_eq, hconjA_apply] using h1
    have hτpos := hpos hreal.embedding
    have hval : σ yE = ((hreal.embedding yE : ℝ) : ℂ) := (hreal.coe_embedding_apply yE).symm
    rw [hval, Complex.norm_real, Real.norm_of_nonneg hτpos.le]
    exact div_self (Complex.ofReal_ne_zero.mpr hτpos.ne')
  have hprod1 : ∏ σ : E →ₐ[k] ℂ, (σ yE / (‖σ yE‖ : ℂ)) = 1 :=
    Finset.prod_involution (fun σ _ => conjA σ) (fun σ _ => hf_pair σ)
      (fun σ _ h => hf_fixed σ h) (fun σ _ => Finset.mem_univ _) (fun σ _ => hconjA_invol σ)
  have hsplit : ∀ σ : E →ₐ[k] ℂ, σ yE = σ yE / (‖σ yE‖ : ℂ) * (‖σ yE‖ : ℂ) := fun σ =>
    (div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (hσ0 σ)))).symm
  have hprodR : ∏ σ : E →ₐ[k] ℂ, σ yE = ((∏ σ : E →ₐ[k] ℂ, ‖σ yE‖ : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    calc ∏ σ : E →ₐ[k] ℂ, σ yE
        = ∏ σ : E →ₐ[k] ℂ, (σ yE / (‖σ yE‖ : ℂ) * (‖σ yE‖ : ℂ)) :=
          Finset.prod_congr rfl fun σ _ => hsplit σ
      _ = (∏ σ : E →ₐ[k] ℂ, (σ yE / (‖σ yE‖ : ℂ))) * ∏ σ : E →ₐ[k] ℂ, (‖σ yE‖ : ℂ) :=
          Finset.prod_mul_distrib
      _ = ∏ σ : E →ₐ[k] ℂ, (‖σ yE‖ : ℂ) := by rw [hprod1, one_mul]
  have hbridge : algebraMap k ℂ (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y))
      = ∏ σ : E →ₐ[k] ℂ, σ yE := by
    rw [Algebra.algebraMap_intNorm (A := 𝓞 k) (B := 𝓞 E) (K := k) (L := E)]
    exact Algebra.norm_eq_prod_embeddings (K := k) (L := E) (E := ℂ) yE
  have hfinal : ((τ' (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y)) : ℝ) : ℂ)
      = ((∏ σ : E →ₐ[k] ℂ, ‖σ yE‖ : ℝ) : ℂ) := by
    rw [show ((τ' (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y)) : ℝ) : ℂ)
        = algebraMap k ℂ (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y)) from rfl,
      hbridge, hprodR]
  have hval := Complex.ofReal_injective hfinal
  rw [hval]
  exact Finset.prod_pos fun σ _ => norm_pos_iff.mpr (hσ0 σ)

end M4aP2
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.Deep.NTSupply NumberField IsDedekindDomain"

open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff relNormCTM"
p2m_open "HeckeCharacter"

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private theorem intNorm_ne_zero {α : 𝓞 E} (hα : α ≠ 0) : Algebra.intNorm (𝓞 k) (𝓞 E) α ≠ 0 := by
  intro h
  have : Ideal.relNorm (𝓞 k) (Ideal.span {α}) = (⊥ : Ideal (𝓞 k)) := by
    rw [Ideal.relNorm_singleton, h, Ideal.span_singleton_eq_bot]
  exact hα (Ideal.span_singleton_eq_bot.mp (Ideal.relNorm_eq_bot_iff.mp this))

end HeckeCharacter
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.Deep.NTSupply NumberField IsDedekindDomain"

open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff relNormCTM"
p2m_open "HeckeCharacter"

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private theorem fracRelNormUnit_principalUnit' (a : 𝓞 E) (ha : a ≠ 0) :
    fracRelNormUnit k E (principalUnit E a ha)
      = principalUnit k (Algebra.intNorm (𝓞 k) (𝓞 E) a) (intNorm_ne_zero k E ha) :=
  Units.ext ((fracRelNormUnit_principalUnit k E a ha).trans
    (principalUnit_val k _ (intNorm_ne_zero k E ha)).symm)

end HeckeCharacter
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.Deep.NTSupply NumberField IsDedekindDomain"

open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff relNormCTM"
p2m_open "HeckeCharacter"

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private theorem coe_relNormCTM {𝔠 : Ideal (𝓞 k)} (Y : ↥(coprimeToModulus E (modulusExt k E 𝔠))) :
    ((relNormCTM k E 𝔠 Y : ↥(coprimeToModulus k 𝔠)) : (FractionalIdeal ((𝓞 k)⁰) k)ˣ)
      = fracRelNormUnit k E (Y : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) := rfl

private theorem relNormCTM_primeUnit {𝔠 : Ideal (𝓞 k)} {w : HeightOneSpectrum (𝓞 E)}
    (hw : ¬ w.asIdeal ∣ modulusExt k E 𝔠) :
    ((relNormCTM k E 𝔠 ⟨primeUnit E w, primeUnit_mem_coprimeToModulus E hw⟩
        : ↥(coprimeToModulus k 𝔠)) : (FractionalIdeal ((𝓞 k)⁰) k)ˣ)
      = primeUnit k (placeUnder' k E w)
          ^ ((placeUnder' k E w).asIdeal.inertiaDeg' w.asIdeal) := by
  exact fracRelNormUnit_primeUnit k E w (placeUnder' k E w) (placeUnder'_asIdeal k E w).symm

end HeckeCharacter
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.Deep.NTSupply"

open scoped nonZeroDivisors IsMulCommutative

section Carriers

variable (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K))

private theorem primeCarrier_mem (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣) :
    primeCarrier K 𝔣 v hv ∈ primeCarriers K 𝔣 :=
  ⟨v, hv, rfl⟩

open Classical in

private def carrierOrOne (v : HeightOneSpectrum (𝓞 K)) : ↥(coprimeToModulus K 𝔣) :=
  if hv : v.asIdeal ∣ 𝔣 then 1 else primeCarrier K 𝔣 v hv

private theorem carrierOrOne_mem_closure (v : HeightOneSpectrum (𝓞 K)) :
    carrierOrOne K 𝔣 v ∈ Subgroup.closure (primeCarriers K 𝔣) := by
  unfold carrierOrOne
  split_ifs with hv
  · exact one_mem _
  · exact Subgroup.subset_closure (primeCarrier_mem K 𝔣 v hv)

open Classical in

private theorem val_carrierOrOne_zpow (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    (((carrierOrOne K 𝔣 v ^ n : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)
      = if v.asIdeal ∣ 𝔣 then 1 else (v.asIdeal : FractionalIdeal ((𝓞 K)⁰) K) ^ n := by
  rw [SubgroupClass.coe_zpow, Units.val_zpow_eq_zpow_val]
  unfold carrierOrOne
  split_ifs with hv
  · rw [OneMemClass.coe_one, Units.val_one, one_zpow]
  · rw [primeCarrier, primeUnit_val]

private theorem raySymbolHom_carrierOrOne (I : ↥(coprimeToModulus K 𝔣)) : raySymbolHom K 𝔣 (carrierOrOne K 𝔣) I = I := by
  apply Subtype.ext
  apply Units.ext
  rw [raySymbolHom_apply]
  unfold raySymbol
  have hfin := hasFiniteMulSupport_raySymbol_factors K (carrierOrOne K 𝔣)
    ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)

  let φ : ↥(coprimeToModulus K 𝔣) →* FractionalIdeal ((𝓞 K)⁰) K :=
    (Units.coeHom (FractionalIdeal ((𝓞 K)⁰) K)).comp (coprimeToModulus K 𝔣).subtype
  show φ (∏ᶠ v, carrierOrOne K 𝔣 v ^ FractionalIdeal.count K v
      ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)) = φ I
  rw [MonoidHom.map_finprod φ hfin]
  conv_rhs => rw [show φ I = ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) from rfl,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K (Units.ne_zero (I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ))]
  refine finprod_congr fun v => ?_
  rw [show φ (carrierOrOne K 𝔣 v ^ FractionalIdeal.count K v ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K))
      = (((carrierOrOne K 𝔣 v ^ FractionalIdeal.count K v ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)
          : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) from rfl,
    val_carrierOrOne_zpow]
  split_ifs with hv
  · rw [I.2 v hv, zpow_zero]
  · rfl

private theorem closure_primeCarriers_eq_top : Subgroup.closure (primeCarriers K 𝔣) = ⊤ := by
  rw [eq_top_iff]
  intro I _
  rw [← raySymbolHom_carrierOrOne K 𝔣 I, raySymbolHom_apply]
  unfold raySymbol
  exact finprod_induction (· ∈ Subgroup.closure (primeCarriers K 𝔣)) (one_mem _) (fun _ _ => mul_mem)
    fun v => zpow_mem (carrierOrOne_mem_closure K 𝔣 v) _

end Carriers
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.Deep.NTSupply NumberField IsDedekindDomain"

open scoped nonZeroDivisors

namespace LanglandsTunnell
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

section hNP

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.HeckeCharacter"

private theorem relNormCTM_primeCarrier_of_inertiaDeg_eq_one {𝔠 : Ideal (𝓞 k)} {w : HeightOneSpectrum (𝓞 E)}
    (hw : ¬ w.asIdeal ∣ modulusExt k E 𝔠) {v : HeightOneSpectrum (𝓞 k)} (hv : ¬ v.asIdeal ∣ 𝔠)
    (hwv : w.asIdeal.under (𝓞 k) = v.asIdeal) (hf : v.asIdeal.inertiaDeg' w.asIdeal = 1) :
    relNormCTM k E 𝔠 ⟨primeUnit E w, primeUnit_mem_coprimeToModulus E hw⟩
      = ⟨primeUnit k v, primeUnit_mem_coprimeToModulus k hv⟩ := by
  have heq : placeUnder' k E w = v :=
    IsDedekindDomain.HeightOneSpectrum.ext (by rw [placeUnder'_asIdeal, hwv])
  exact Subtype.ext (by rw [relNormCTM_primeUnit k E hw, heq, hf, pow_one])

end hNP
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.Deep.NTSupply IntermediateField"

open scoped nonZeroDivisors IsMulCommutative

section Onto

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  [IsMulCommutative (M ≃ₐ[K] M)]

private def NoTotallySplitSub (𝔣 : Ideal (𝓞 K)) : Prop :=
  ∀ F' : IntermediateField K M, F' ≠ ⊥ →
    ∃ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 ∧ ∃ x : M, x ∈ F' ∧ artinFrob K M v x ≠ x

private theorem artinFrob_mem_range_artinSymbol (𝔣 : Ideal (𝓞 K)) {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣) :
    artinFrob K M v ∈ (artinSymbol K M 𝔣).range :=
  ⟨primeCarrier K 𝔣 v hv, by rw [primeCarrier, artinSymbol_prime K M hv]⟩

private theorem artinFrob_apply_eq_self_of_mem_fixedField (𝔣 : Ideal (𝓞 K)) {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣)
    {x : M} (hx : x ∈ fixedField (artinSymbol K M 𝔣).range) : artinFrob K M v x = x :=
  (mem_fixedField_iff _ x).mp hx _ (artinFrob_mem_range_artinSymbol K M 𝔣 hv)

private theorem artinSymbol_surjective (𝔣 : Ideal (𝓞 K)) (h : NoTotallySplitSub K M 𝔣) : Function.Surjective (artinSymbol K M 𝔣) := by
  rw [← MonoidHom.range_eq_top]
  set H := (artinSymbol K M 𝔣).range with hH
  have hbot : fixedField H = ⊥ := by
    by_contra hne
    obtain ⟨v, hv, x, hx, hne'⟩ := h (fixedField H) hne
    exact hne' (artinFrob_apply_eq_self_of_mem_fixedField K M 𝔣 hv hx)
  rw [← fixingSubgroup_fixedField H, hbot, fixingSubgroup_bot]

end Onto
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.Deep.NTSupply NumberField IsDedekindDomain"

open scoped nonZeroDivisors

namespace LanglandsTunnell
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

section Pincer

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.HeckeCharacter"

private theorem ker_artinSymbol_eq_normRaySubgroup (𝔣 : Ideal (𝓞 K))
    (hle : normRaySubgroup K L 𝔣 ≤ (artinSymbol K L 𝔣).ker)
    (h : NoTotallySplitSub K L 𝔣)
    (hCSb : SecondInequalityCTM K L 𝔣) :
    (artinSymbol K L 𝔣).ker = normRaySubgroup K L 𝔣 := by
  have hGpos : 0 < Nat.card (L ≃ₐ[K] L) := Nat.card_pos
  haveI : (normRaySubgroup K L 𝔣).FiniteIndex :=
    ⟨fun h0 => absurd (h0 ▸ hCSb) (fun h' => hGpos.ne' (Nat.eq_zero_of_zero_dvd h'))⟩
  have hker_idx : (artinSymbol K L 𝔣).ker.index = Nat.card (L ≃ₐ[K] L) := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (artinSymbol_surjective K L 𝔣 h),
      Nat.card_congr Subgroup.topEquiv.toEquiv]
  have heq : (normRaySubgroup K L 𝔣).index = (artinSymbol K L 𝔣).ker.index :=
    le_antisymm (hker_idx ▸ Nat.le_of_dvd hGpos hCSb) (Subgroup.index_antitone hle)
  refine le_antisymm (Subgroup.relIndex_eq_one.mp ?_) hle
  have hmul := Subgroup.relIndex_mul_index hle
  rw [heq] at hmul
  exact (mul_eq_right₀ (hker_idx ▸ hGpos.ne')).mp hmul

private theorem relNormCTM_range_le_ker_artinSymbol (𝔣 : Ideal (𝓞 K))
    (hfrob : ∀ w : HeightOneSpectrum (𝓞 L), ¬ (placeUnder' K L w).asIdeal ∣ 𝔣 →
      artinFrob K L (placeUnder' K L w) ^ (placeUnder' K L w).asIdeal.inertiaDeg' w.asIdeal = 1) :
    (relNormCTM K L 𝔣).range ≤ (artinSymbol K L 𝔣).ker := by
  rw [MonoidHom.range_le_ker_iff]
  apply MonoidHom.eq_of_eqOn_dense (closure_primeCarriers_eq_top L (modulusExt K L 𝔣))
  rintro _ ⟨w, hw, rfl⟩
  have hv : ¬ (placeUnder' K L w).asIdeal ∣ 𝔣 := fun h => hw ((placeUnder'_dvd_iff K L 𝔣 w).mp h)
  show artinSymbol K L 𝔣 (relNormCTM K L 𝔣 ⟨primeUnit L w, primeUnit_mem_coprimeToModulus L hw⟩) = 1
  rw [show relNormCTM K L 𝔣 ⟨primeUnit L w, primeUnit_mem_coprimeToModulus L hw⟩
        = (⟨primeUnit K (placeUnder' K L w), primeUnit_mem_coprimeToModulus K hv⟩
            : ↥(coprimeToModulus K 𝔣)) ^ (placeUnder' K L w).asIdeal.inertiaDeg' w.asIdeal from
      Subtype.ext (relNormCTM_primeUnit K L hw),
    map_pow, artinSymbol_prime K L hv]
  exact hfrob w hv

private theorem normRaySubgroup_le_ker_artinSymbol (𝔣 : Ideal (𝓞 K))
    (hP_ker : (narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣) ≤ (artinSymbol K L 𝔣).ker)
    (hfrob : ∀ w : HeightOneSpectrum (𝓞 L), ¬ (placeUnder' K L w).asIdeal ∣ 𝔣 →
      artinFrob K L (placeUnder' K L w) ^ (placeUnder' K L w).asIdeal.inertiaDeg' w.asIdeal = 1) :
    normRaySubgroup K L 𝔣 ≤ (artinSymbol K L 𝔣).ker :=
  sup_le hP_ker (relNormCTM_range_le_ker_artinSymbol K L 𝔣 hfrob)

end Pincer
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section

section

set_option autoImplicit false

namespace LanglandsTunnell
namespace P5
p2m_open "LanglandsTunnell"

p2m_open "NumberField Ideal NumberField.Ideal Matrix FLT.ExplicitLift"

open LanglandsTunnell.P0

open scoped Pointwise

section FrobeniusGrain

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]

omit [IsGalois ℚ L] in

private theorem inertia_smul_eq_bot (τ : L ≃ₐ[ℚ] L) (Q : Ideal (𝓞 L)) (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥) :
    (τ • Q).inertia (L ≃ₐ[ℚ] L) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hg' : ∀ x : 𝓞 L, g • x - x ∈ τ • Q := fun x => AddSubgroup.mem_inertia.1 hg x
  have hmem : τ⁻¹ * g * τ ∈ Q.inertia (L ≃ₐ[ℚ] L) := by
    refine AddSubgroup.mem_inertia.2 fun x => ?_
    have hx := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 (hg' (τ • x))
    rw [smul_sub, inv_smul_smul, ← mul_smul, ← mul_smul] at hx
    exact hx
  rw [hI, Subgroup.mem_bot] at hmem
  have hgg : g = τ * (τ⁻¹ * g * τ) * τ⁻¹ := by group
  rw [hmem] at hgg
  simpa using hgg

private theorem arithFrobAt_smul (τ : L ≃ₐ[ℚ] L) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Finite (𝓞 L ⧸ Q)]
    [Finite (𝓞 L ⧸ (τ • Q))] (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥) :
    arithFrobAt ℤ (L ≃ₐ[ℚ] L) (τ • Q) = τ * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q * τ⁻¹ := by
  have h1 : IsArithFrobAt ℤ (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (τ • Q)) (τ • Q) :=
    IsArithFrobAt.arithFrobAt ℤ (L ≃ₐ[ℚ] L) (τ • Q)
  have h2 : IsArithFrobAt ℤ (τ * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q * τ⁻¹) (τ • Q) :=
    (IsArithFrobAt.arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q).conj τ
  have h3 := h1.mul_inv_mem_inertia h2
  rw [inertia_smul_eq_bot τ Q hI, Subgroup.mem_bot] at h3
  exact mul_inv_eq_one.1 h3

end FrobeniusGrain
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end LanglandsTunnell.P5
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.HeckeCharacter"

open scoped nonZeroDivisors IsMulCommutative

section Admissible

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

omit [NumberField K] [IsGalois K L] in

private theorem admissibleExp_pos (v : HeightOneSpectrum (𝓞 K)) : 0 < admissibleExp K v := Nat.succ_pos _

omit [NumberField L] [IsGalois K L] in

private theorem dvd_of_isAdmissibleModulus {𝔣 : Ideal (𝓞 K)} (h : IsAdmissibleModulus K L 𝔣) {v : HeightOneSpectrum (𝓞 K)}
    (hv : (primeAbove K L v).inertia (L ≃ₐ[K] L) ≠ ⊥) : v.asIdeal ∣ 𝔣 :=
  dvd_trans (dvd_pow_self _ (admissibleExp_pos K v).ne') (h.2 v hv)

omit [NumberField L] [IsGalois K L] in

private theorem inertia_eq_bot_of_isAdmissibleModulus {𝔣 : Ideal (𝓞 K)} (h : IsAdmissibleModulus K L 𝔣) (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ v.asIdeal ∣ 𝔣) : (primeAbove K L v).inertia (L ≃ₐ[K] L) = ⊥ :=
  not_ne_iff.mp fun hne => hv (dvd_of_isAdmissibleModulus K L h hne)

end Admissible
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.Deep.NTSupply NumberField IsDedekindDomain"

open scoped nonZeroDivisors IsMulCommutative Pointwise

namespace LanglandsTunnell
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

section Hfrob

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.HeckeCharacter"

attribute [local instance] Ideal.Quotient.field

private theorem artinFrob_pow_inertiaDeg_eq_one (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (hwv : w.asIdeal.under (𝓞 K) = v.asIdeal)
    (hI : (primeAbove K L v).inertia (L ≃ₐ[K] L) = ⊥) :
    artinFrob K L v ^ v.asIdeal.inertiaDeg' w.asIdeal = 1 := by

  have hmem : artinFrob K L v ∈ MulAction.stabilizer (L ≃ₐ[K] L) (primeAbove K L v) :=
    (isArithFrobAt_artinFrob K L v).mem_stabilizer
  haveI hwv' : w.asIdeal.LiesOver v.asIdeal := ⟨hwv.symm⟩

  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  haveI : Finite (𝓞 L ⧸ primeAbove K L v) :=
    Ideal.finiteQuotientOfFreeOfNeBot (primeAbove K L v) (primeAbove_ne_bot K L v)

  have hcard : Nat.card ↥(MulAction.stabilizer (L ≃ₐ[K] L) (primeAbove K L v))
      = v.asIdeal.inertiaDeg' w.asIdeal := by
    rw [Ideal.card_stabilizer_eq (G := L ≃ₐ[K] L) v.asIdeal (primeAbove K L v),
      ← Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) v.asIdeal
        (primeAbove K L v),
      hI, Subgroup.card_bot, one_mul,
      Ideal.inertiaDegIn_eq_inertiaDeg (G := L ≃ₐ[K] L) v.asIdeal w.asIdeal,
      Ideal.inertiaDeg'_eq_inertiaDeg]
  have := pow_card_eq_one'
    (G := ↥(MulAction.stabilizer (L ≃ₐ[K] L) (primeAbove K L v))) (x := ⟨_, hmem⟩)
  rw [hcard] at this
  exact Subtype.ext_iff.mp this

private theorem artinFrob_placeUnder_pow_inertiaDeg_eq_one (w : HeightOneSpectrum (𝓞 L))
    (hI : (primeAbove K L (placeUnder' K L w)).inertia (L ≃ₐ[K] L) = ⊥) :
    artinFrob K L (placeUnder' K L w) ^ (placeUnder' K L w).asIdeal.inertiaDeg' w.asIdeal = 1 :=
  artinFrob_pow_inertiaDeg_eq_one K L (placeUnder' K L w) w (placeUnder'_asIdeal K L w).symm hI

private theorem hfrob_of_isAdmissibleModulus {𝔣 : Ideal (𝓞 K)} (h : IsAdmissibleModulus K L 𝔣)
    (w : HeightOneSpectrum (𝓞 L)) (hv : ¬ (placeUnder' K L w).asIdeal ∣ 𝔣) :
    artinFrob K L (placeUnder' K L w) ^ (placeUnder' K L w).asIdeal.inertiaDeg' w.asIdeal = 1 :=
  artinFrob_placeUnder_pow_inertiaDeg_eq_one K L w
    (inertia_eq_bot_of_isAdmissibleModulus K L h (placeUnder' K L w) hv)

end Hfrob
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section

set_option autoImplicit false

section

p2m_open "NumberField nonZeroDivisors IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.Deep.NTSupply LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin"

open scoped IsMulCommutative

namespace M4aP2

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [IsGalois K M]

open _root_.NumberField.HeightOneSpectrum _root_.IsDedekindDomain.HeightOneSpectrum in
omit [NumberField M] [IsGalois K M] in

private theorem natCast_notMem_primeAbove (q : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (hq : ¬ v.asIdeal ∣ Ideal.span {(q : 𝓞 K)}) :
    (q : 𝓞 M) ∉ primeAbove K M v := by
  intro hmem
  apply hq
  have h1 : (q : 𝓞 K) ∈ (primeAbove K M v).under (𝓞 K) := by
    rw [Ideal.under, Ideal.mem_comap, map_natCast]
    exact hmem
  rw [under_primeAbove] at h1
  rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
  exact h1

open _root_.NumberField.HeightOneSpectrum _root_.IsDedekindDomain.HeightOneSpectrum in

private theorem artinFrob_primitiveRoot {q : ℕ} [NeZero q] {ζ : M} (hζ : IsPrimitiveRoot ζ q)
    (v : HeightOneSpectrum (𝓞 K)) (hq : ¬ v.asIdeal ∣ Ideal.span {(q : 𝓞 K)}) :
    artinFrob K M v ζ = ζ ^ Ideal.absNorm v.asIdeal := by
  classical
  have hq0 : q ≠ 0 := NeZero.ne q
  have hint : IsIntegral ℤ ζ :=
    ⟨Polynomial.X ^ q - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hq0, by
      simp [hζ.pow_eq_one]⟩
  let ζO : 𝓞 M := ⟨ζ, hint⟩
  have hpow : ζO ^ q = 1 := Subtype.coe_injective (by push_cast; exact hζ.pow_eq_one)
  have H : (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 M) (artinFrob K M v)).IsArithFrobAt
      (primeAbove K M v) := isArithFrobAt_artinFrob K M v
  have h2 := H.apply_of_pow_eq_one hpow (natCast_notMem_primeAbove K M q v hq)
  have hcard : Nat.card (𝓞 K ⧸ (primeAbove K M v).under (𝓞 K)) = Ideal.absNorm v.asIdeal := by
    rw [under_primeAbove, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hcard] at h2
  have h3 := congrArg (algebraMap (𝓞 M) M) h2
  rw [map_pow] at h3
  exact h3

open _root_.NumberField.HeightOneSpectrum _root_.IsDedekindDomain.HeightOneSpectrum in

private theorem autToPow_artinFrob {q : ℕ} [NeZero q] {ζ : M} (hζ : IsPrimitiveRoot ζ q)
    (v : HeightOneSpectrum (𝓞 K)) (hq : ¬ v.asIdeal ∣ Ideal.span {(q : 𝓞 K)}) :
    hζ.autToPow K (artinFrob K M v) = normClass K q v := by
  have hact := artinFrob_primitiveRoot K M hζ v hq
  have hcop := absNorm_coprime_of_not_dvd K q v hq
  refine Units.ext ?_
  rw [normClass_coe K q v hcop]
  have hspec := hζ.autToPow_spec K (artinFrob K M v)
  have hordζ : orderOf ζ = q := hζ.eq_orderOf.symm
  have hval : ζ ^ ((Ideal.absNorm v.asIdeal : ZMod q)).val = ζ ^ Ideal.absNorm v.asIdeal := by
    rw [ZMod.val_natCast, ← hordζ]
    exact pow_mod_orderOf ζ _
  have hvals : ((hζ.autToPow K (artinFrob K M v) : ZMod q)).val
      = ((Ideal.absNorm v.asIdeal : ZMod q)).val :=
    hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (by rw [hspec, hact]; exact hval.symm)
  exact ZMod.val_injective q hvals

open _root_.NumberField.HeightOneSpectrum _root_.IsDedekindDomain.HeightOneSpectrum in

private theorem autToPow_artinSymbol {q : ℕ} [NeZero q] {ζ : M} (hζ : IsPrimitiveRoot ζ q)
    [IsMulCommutative (M ≃ₐ[K] M)] {𝔣 : Ideal (𝓞 K)}
    (hq𝔣 : Ideal.span {(q : 𝓞 K)} ∣ 𝔣) (I : coprimeToModulus K 𝔣) :
    hζ.autToPow K (artinSymbol K M 𝔣 I) = raySymbol K (normClass K q) I.1 := by
  have hunf : artinSymbol K M 𝔣 I = raySymbolHom K 𝔣 (artinFrob K M) I := rfl
  rw [hunf, raySymbolHom_apply, map_raySymbol]
  unfold raySymbol
  refine finprod_congr fun v => ?_
  by_cases hcv : FractionalIdeal.count K v
      ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) = 0
  · rw [hcv, zpow_zero, zpow_zero]
  · have hv𝔣 : ¬ v.asIdeal ∣ 𝔣 := fun hdvd => hcv ((mem_coprimeToModulus_iff K).mp I.2 v hdvd)
    have hvq : ¬ v.asIdeal ∣ Ideal.span {(q : 𝓞 K)} := fun h => hv𝔣 (h.trans hq𝔣)
    simp only [Function.comp_apply]
    rw [autToPow_artinFrob K M hζ v hvq]

end M4aP2
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section

set_option autoImplicit false

namespace LanglandsTunnell
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

open IntermediateField

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

variable (L : IntermediateField K M) [IsGalois K L]

variable {m : ℕ} [NeZero m] {ζ : M} (hζ : IsPrimitiveRoot ζ m)

variable {C : Type*} [Group C] (ψ : (ZMod m)ˣ ≃* C)

private theorem autToPow_eq_one_iff (τ : M ≃ₐ[K] M) : hζ.autToPow K τ = 1 ↔ τ ζ = ζ := by
  have key : ∀ v : ℕ, ζ ^ v = ζ ↔ (v : ZMod m) = 1 := fun v => by
    rw [show (ζ ^ v = ζ ↔ ζ ^ v = ζ ^ 1) by rw [pow_one], (hζ.isOfFinOrder (NeZero.ne m)).pow_eq_pow_iff_modEq,
      ← hζ.eq_orderOf, ← ZMod.natCast_eq_natCast_iff, Nat.cast_one]
  rw [← hζ.autToPow_spec K τ, key, ZMod.natCast_zmod_val, Units.val_eq_one]

private theorem mem_fixingSubgroup_intermediateField_iff (E : IntermediateField K M) (τ : M ≃ₐ[K] M) :
    τ ∈ E.fixingSubgroup ↔ ∀ x ∈ E, τ x = x :=
  _root_.mem_fixingSubgroup_iff _

private theorem apply_eq_self_iff_mem_fixingSubgroup_adjoin (τ : M ≃ₐ[K] M) : τ ζ = ζ ↔ τ ∈ K⟮ζ⟯.fixingSubgroup := by
  rw [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, adjoin_simple_le_iff, mem_fixedField_iff]
  constructor
  · intro h g hg
    exact (Subgroup.zpowers_le.mpr (show τ ∈ MulAction.stabilizer (M ≃ₐ[K] M) ζ from h) : _ ≤ _) hg
  · intro h
    exact h τ (Subgroup.mem_zpowers τ)

variable [FiniteDimensional K M]

variable [IsGalois K M]

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField IsDedekindDomain IntermediateField Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.Deep.NTSupply"

open scoped nonZeroDivisors IsMulCommutative

section Cyclotomic

variable (K M : Type*) [Field K] [Field M] [Algebra K M]

variable {q : ℕ} [NeZero q] {ζ : M} (hζ : IsPrimitiveRoot ζ q)

private theorem eq_one_of_autToPow_eq_one (htop : K⟮ζ⟯ = ⊤) {τ : M ≃ₐ[K] M} (h : hζ.autToPow K τ = 1) : τ = 1 := by
  have hfix : τ ∈ K⟮ζ⟯.fixingSubgroup :=
    (apply_eq_self_iff_mem_fixingSubgroup_adjoin τ).mp ((autToPow_eq_one_iff hζ τ).mp h)
  rw [htop, mem_fixingSubgroup_intermediateField_iff] at hfix
  exact AlgEquiv.ext fun x => hfix x IntermediateField.mem_top

variable [NumberField K] [NumberField M] [IsGalois K M] [IsMulCommutative (M ≃ₐ[K] M)]

include hζ in

private theorem artinSymbol_eq_one_of_ray (htop : K⟮ζ⟯ = ⊤) {𝔣 : Ideal (𝓞 K)} (hq𝔣 : Ideal.span {(q : 𝓞 K)} ∣ 𝔣)
    (I : ↥(coprimeToModulus K 𝔣)) {α : 𝓞 K} (hα0 : α ≠ 0) (hα1 : α - 1 ∈ 𝔣)
    (hpos : ∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α))
    (hI : ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)
      = ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K)) :
    artinSymbol K M 𝔣 I = 1 := by
  refine eq_one_of_autToPow_eq_one K M hζ htop ?_
  rw [M4aP2.autToPow_artinSymbol K M hζ hq𝔣 I]
  have h := M4aP2.normClassKillsRay K q hq𝔣 α hα0 hα1 hpos
  rw [← hI] at h
  exact h

end Cyclotomic
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section Sub

variable (K F M : Type*) [Field K] [NumberField K] [Field F] [NumberField F] [Field M] [NumberField M]
  [Algebra K F] [Algebra K M] [Algebra F M] [IsScalarTower K F M] [IsGalois K F] [IsGalois K M]
  [IsMulCommutative (F ≃ₐ[K] F)] [IsMulCommutative (M ≃ₐ[K] M)]

variable {q : ℕ} [NeZero q] {ζ : M} (hζ : IsPrimitiveRoot ζ q)

include hζ in

private theorem artinSymbol_sub_eq_one_of_ray (htop : K⟮ζ⟯ = ⊤) {𝔣 : Ideal (𝓞 K)} (hq𝔣 : Ideal.span {(q : 𝓞 K)} ∣ 𝔣)
    (hunr : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 → ((primeAbove K M v).under (𝓞 F)).inertia (F ≃ₐ[K] F) = ⊥)
    (I : ↥(coprimeToModulus K 𝔣)) {α : 𝓞 K} (hα0 : α ≠ 0) (hα1 : α - 1 ∈ 𝔣)
    (hpos : ∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α))
    (hI : ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)
      = ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K)) :
    artinSymbol K F 𝔣 I = 1 := by
  rw [← restrictNormalHom_artinSymbol K F M 𝔣 hunr I, artinSymbol_eq_one_of_ray K M hζ htop hq𝔣 I hα0 hα1 hpos hI, map_one]

end Sub
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section

set_option autoImplicit false

namespace LanglandsTunnell
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.Deep.NTSupply IntermediateField"

open scoped nonZeroDivisors IsMulCommutative

section Group

variable {G : Type*} [CommGroup G] [Finite G]

private theorem isSimpleGroup_quotient_of_isCoatom {H : Subgroup G} (hH : IsCoatom H) : IsSimpleGroup (G ⧸ H) := by
  haveI : Nontrivial (G ⧸ H) := by
    rw [← Finite.one_lt_card_iff_nontrivial, ← Subgroup.index]
    exact Subgroup.one_lt_index_of_ne_top hH.1
  refine ⟨fun N _ => ?_⟩
  have hle : H ≤ N.comap (QuotientGroup.mk' H) := by
    intro x hx
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem N
  have hinj := Subgroup.comap_injective (QuotientGroup.mk'_surjective H)
  rcases hH.le_iff.mp hle with htop | heq
  · right
    exact hinj (htop.trans (Subgroup.comap_top _).symm)
  · left
    refine hinj (heq.trans ?_)
    rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']

private theorem index_prime_of_isCoatom {H : Subgroup G} (hH : IsCoatom H) : H.index.Prime := by
  haveI := isSimpleGroup_quotient_of_isCoatom hH
  exact IsSimpleGroup.prime_card

end Group
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section Field

variable (K M : Type*) [Field K] [Field M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
  [IsMulCommutative (M ≃ₐ[K] M)]

omit [IsMulCommutative (M ≃ₐ[K] M)] in

private theorem finrank_fixedField_eq_index (H : Subgroup (M ≃ₐ[K] M)) : Module.finrank K (fixedField H) = H.index := by
  have h1 : Module.finrank K (fixedField H) * Module.finrank (fixedField H) M = Module.finrank K M := Module.finrank_mul_finrank K _ M
  rw [finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank K M] at h1
  have h2 := H.index_mul_card
  have hpos : 0 < Nat.card H := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

private theorem exists_le_finrank_prime (F' : IntermediateField K M) (hF' : F' ≠ ⊥) :
    ∃ F : IntermediateField K M, F ≤ F' ∧ (Module.finrank K F).Prime := by
  have hne : F'.fixingSubgroup ≠ ⊤ := fun h => hF' (by
    rw [← IsGalois.fixedField_fixingSubgroup F', h, ← IntermediateField.fixingSubgroup_bot, IsGalois.fixedField_fixingSubgroup])
  obtain ⟨Hm, hcoatom, hle⟩ := (eq_top_or_exists_le_coatom F'.fixingSubgroup).resolve_left hne
  refine ⟨fixedField Hm, ?_, ?_⟩
  · calc fixedField Hm ≤ fixedField F'.fixingSubgroup := fixedField_le hle
      _ = F' := IsGalois.fixedField_fixingSubgroup F'
  · rw [finrank_fixedField_eq_index]
    exact index_prime_of_isCoatom hcoatom

omit [IsMulCommutative (M ≃ₐ[K] M)] in

private theorem isGalois_intermediateField [IsMulCommutative (M ≃ₐ[K] M)] (F : IntermediateField K M) : IsGalois K F := by
  rw [← IsGalois.fixedField_fixingSubgroup F]
  infer_instance

end Field
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section Contract

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]

private def NoTotallySplitPrimeSub (𝔣 : Ideal (𝓞 K)) : Prop :=
  ∀ F : IntermediateField K M, (Module.finrank K F).Prime →
    ∃ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 ∧ ∃ x : M, x ∈ F ∧ artinFrob K M v x ≠ x

variable {K M}

private theorem NoTotallySplitPrimeSub.noTotallySplitSub [IsMulCommutative (M ≃ₐ[K] M)] {𝔣 : Ideal (𝓞 K)} (h : NoTotallySplitPrimeSub K M 𝔣) :
    NoTotallySplitSub K M 𝔣 := by
  intro F' hF'
  obtain ⟨F, hle, hp⟩ := exists_le_finrank_prime K M F' hF'
  obtain ⟨v, hv, x, hx, hne⟩ := h F hp
  exact ⟨v, hv, x, hle hx, hne⟩

end Contract
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

open NumberField IsDedekindDomain IntermediateField Polynomial

section DegreeOne

attribute [local instance] Ideal.Quotient.field

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

variable (E : IntermediateField K M)

variable {E}

variable [NumberField K] [NumberField M] [IsGalois K M]

private theorem card_quot_under_eq_of_fix {τ : M ≃ₐ[K] M} (hτ : τ ∈ E.fixingSubgroup) (Q : Ideal (𝓞 M)) [Q.IsMaximal]
    (H : IsArithFrobAt (𝓞 K) τ Q) :
    Nat.card (𝓞 E ⧸ Q.under (𝓞 E)) = Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) := by
  classical
  haveI hP : (Q.under (𝓞 E)).IsMaximal := Ideal.IsMaximal.under (𝓞 E) Q
  haveI hp : (Q.under (𝓞 K)).IsMaximal := Ideal.IsMaximal.under (𝓞 K) Q
  have hpP : (Q.under (𝓞 E)).under (𝓞 K) = Q.under (𝓞 K) := Ideal.under_under Q
  haveI : (Q.under (𝓞 E)).LiesOver (Q.under (𝓞 K)) := ⟨hpP.symm⟩
  have hPne : Q.under (𝓞 E) ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)
  have hpne : Q.under (𝓞 K) ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField K)
  haveI : Finite (𝓞 E ⧸ Q.under (𝓞 E)) := Ideal.finiteQuotientOfFreeOfNeBot _ hPne
  haveI : Finite (𝓞 K ⧸ Q.under (𝓞 K)) := Ideal.finiteQuotientOfFreeOfNeBot _ hpne
  set q := Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) with hqdef
  have hq1 : 1 < q := Finite.one_lt_card

  have hge : q ≤ Nat.card (𝓞 E ⧸ Q.under (𝓞 E)) :=
    Nat.card_le_card_of_injective _ (algebraMap (𝓞 K ⧸ Q.under (𝓞 K)) (𝓞 E ⧸ Q.under (𝓞 E))).injective

  have hfix : ∀ a : 𝓞 E, τ • algebraMap (𝓞 E) (𝓞 M) a = algebraMap (𝓞 E) (𝓞 M) a := fun a =>
    RingOfIntegers.ext ((mem_fixingSubgroup_intermediateField_iff E τ).mp hτ _ (a : E).2)
  have hroot : ∀ y : 𝓞 E ⧸ Q.under (𝓞 E), y ^ q = y := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_pow, eq_comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.under_def, Ideal.mem_comap, map_sub, map_pow]
    have h := H (algebraMap (𝓞 E) (𝓞 M) a)
    rw [MulSemiringAction.toAlgHom_apply, hfix] at h
    exact h
  have hle : Nat.card (𝓞 E ⧸ Q.under (𝓞 E)) ≤ q := by
    letI := Fintype.ofFinite (𝓞 E ⧸ Q.under (𝓞 E))
    have hne : (X ^ q - X : (𝓞 E ⧸ Q.under (𝓞 E))[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ hq1
    have hsub : (Finset.univ : Finset (𝓞 E ⧸ Q.under (𝓞 E))).val ⊆ (X ^ q - X : (𝓞 E ⧸ Q.under (𝓞 E))[X]).roots := by
      intro y _
      rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def, eval_sub, eval_pow, eval_X, hroot y, sub_self]
    have h := Polynomial.card_le_degree_of_subset_roots hsub
    rwa [Finset.card_univ, FiniteField.X_pow_card_sub_X_natDegree_eq _ hq1, ← Nat.card_eq_fintype_card] at h
  exact le_antisymm hle hge

private theorem inertiaDeg_under_eq_one_of_fix {τ : M ≃ₐ[K] M} (hτ : τ ∈ E.fixingSubgroup) (Q : Ideal (𝓞 M)) [Q.IsMaximal]
    (H : IsArithFrobAt (𝓞 K) τ Q) :
    (Q.under (𝓞 K)).inertiaDeg' (Q.under (𝓞 E)) = 1 := by
  classical
  haveI hP : (Q.under (𝓞 E)).IsMaximal := Ideal.IsMaximal.under (𝓞 E) Q
  haveI hp : (Q.under (𝓞 K)).IsMaximal := Ideal.IsMaximal.under (𝓞 K) Q
  haveI : (Q.under (𝓞 E)).LiesOver (Q.under (𝓞 K)) := ⟨(Ideal.under_under Q).symm⟩
  have hPne : Q.under (𝓞 E) ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)
  have hpne : Q.under (𝓞 K) ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField K)
  haveI : Finite (𝓞 E ⧸ Q.under (𝓞 E)) := Ideal.finiteQuotientOfFreeOfNeBot _ hPne
  haveI : Finite (𝓞 K ⧸ Q.under (𝓞 K)) := Ideal.finiteQuotientOfFreeOfNeBot _ hpne
  have hq1 : 1 < Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) := Finite.one_lt_card
  have hcard := card_quot_under_eq_of_fix hτ Q H
  have hpow := Module.natCard_eq_pow_finrank (K := 𝓞 K ⧸ Q.under (𝓞 K)) (V := 𝓞 E ⧸ Q.under (𝓞 E))
  rw [hcard] at hpow
  rw [Ideal.inertiaDeg_algebraMap]
  have h1 : Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) ^ Module.finrank (𝓞 K ⧸ Q.under (𝓞 K)) (𝓞 E ⧸ Q.under (𝓞 E))
      = Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) ^ 1 := by
    rw [pow_one]; exact hpow.symm
  exact Nat.pow_right_injective hq1 h1

end DegreeOne
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section

set_option autoImplicit false

namespace LanglandsTunnell
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.Deep.NTSupply IntermediateField HeckeCharacter P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.HeckeCharacter"

open scoped nonZeroDivisors IsMulCommutative

section Under

variable (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K))

private theorem not_dvd_modulusExt_of_under {E : Type*} [Field E] [NumberField E] [Algebra K E]
    {w : HeightOneSpectrum (𝓞 E)} {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣)
    (hwv : w.asIdeal.under (𝓞 K) = v.asIdeal) : ¬ w.asIdeal ∣ modulusExt K E 𝔣 := fun h => hv (by
  rw [Ideal.dvd_iff_le] at h ⊢
  rw [← hwv]
  exact Ideal.map_le_iff_le_comap.mp h)

variable (M : Type*) [Field M] [NumberField M] [Algebra K M] (F : IntermediateField K M)

private noncomputable def primeUnderIn (v : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 F) :=
  ⟨(primeAbove K M v).under (𝓞 F), ((primeAbove_isMaximal K M v).under (𝓞 F)).isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField ((primeAbove_isMaximal K M v).under (𝓞 F)) (RingOfIntegers.not_isField F)⟩

private theorem primeUnderIn_asIdeal (v : HeightOneSpectrum (𝓞 K)) : (primeUnderIn K M F v).asIdeal = (primeAbove K M v).under (𝓞 F) := rfl

private theorem primeUnderIn_under (v : HeightOneSpectrum (𝓞 K)) : (primeUnderIn K M F v).asIdeal.under (𝓞 K) = v.asIdeal := by
  rw [primeUnderIn_asIdeal, Ideal.under_under, under_primeAbove]

end Under
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section Split

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  (F : IntermediateField K M) (𝔣 : Ideal (𝓞 K))

private theorem inertiaDeg_primeUnderIn_eq_one (v : HeightOneSpectrum (𝓞 K)) (hfix : ∀ x : M, x ∈ F → artinFrob K M v x = x) :
    v.asIdeal.inertiaDeg' (primeUnderIn K M F v).asIdeal = 1 := by
  have h := inertiaDeg_under_eq_one_of_fix (E := F) ((mem_fixingSubgroup_iff F _).mpr hfix) (primeAbove K M v)
    (isArithFrobAt_artinFrob K M v)
  rwa [under_primeAbove] at h

private theorem primeCarrier_mem_range_relNormCTM (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣)
    (hfix : ∀ x : M, x ∈ F → artinFrob K M v x = x) : primeCarrier K 𝔣 v hv ∈ (relNormCTM K F 𝔣).range :=
  ⟨⟨primeUnit F (primeUnderIn K M F v),
      primeUnit_mem_coprimeToModulus F (not_dvd_modulusExt_of_under K 𝔣 hv (primeUnderIn_under K M F v))⟩,
    relNormCTM_primeCarrier_of_inertiaDeg_eq_one K F (not_dvd_modulusExt_of_under K 𝔣 hv (primeUnderIn_under K M F v)) hv
      (primeUnderIn_under K M F v) (inertiaDeg_primeUnderIn_eq_one K M F v hfix)⟩

private theorem normRaySubgroup_eq_top_of_fix
    (hfix : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 → ∀ x : M, x ∈ F → artinFrob K M v x = x) :
    normRaySubgroup K F 𝔣 = ⊤ := by
  rw [eq_top_iff, ← closure_primeCarriers_eq_top K 𝔣, Subgroup.closure_le]
  rintro _ ⟨v, hv, rfl⟩
  exact Subgroup.mem_sup_right (primeCarrier_mem_range_relNormCTM K M F 𝔣 v hv (hfix v hv))

private theorem index_normRaySubgroup_eq_one_of_fix
    (hfix : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 → ∀ x : M, x ∈ F → artinFrob K M v x = x) :
    (normRaySubgroup K F 𝔣).index = 1 := by
  rw [normRaySubgroup_eq_top_of_fix K M F 𝔣 hfix, Subgroup.index_top]

end Split
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section Reduce

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  [IsMulCommutative (M ≃ₐ[K] M)]

private theorem noTotallySplitPrimeSub_of_firstInequalityCTM (𝔣 : Ideal (𝓞 K))
    (hFI : ∀ F : IntermediateField K M, (Module.finrank K F).Prime → FirstInequalityCTM K F 𝔣) :
    NoTotallySplitPrimeSub K M 𝔣 := by
  intro F hF
  by_contra hcon
  push Not at hcon
  have h1 := hFI F hF
  unfold FirstInequalityCTM at h1
  rw [index_normRaySubgroup_eq_one_of_fix K M F 𝔣 hcon, Nat.dvd_one] at h1
  haveI := isGalois_intermediateField K M F
  rw [IsGalois.card_aut_eq_finrank] at h1
  exact hF.ne_one h1

private theorem noTotallySplitSub_of_firstInequalityCTM (𝔣 : Ideal (𝓞 K))
    (hFI : ∀ F : IntermediateField K M, (Module.finrank K F).Prime → FirstInequalityCTM K F 𝔣) :
    NoTotallySplitSub K M 𝔣 :=
  (noTotallySplitPrimeSub_of_firstInequalityCTM 𝔣 hFI).noTotallySplitSub

end Reduce
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section

set_option autoImplicit false

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.Deep.NTSupply NumberField IsDedekindDomain"

open scoped nonZeroDivisors IsMulCommutative Pointwise

namespace LanglandsTunnell
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

section HkerA

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.HeckeCharacter"

variable (E N Θ : Type*) [Field E] [NumberField E] [Field N] [NumberField N] [Field Θ] [NumberField Θ]
  [Algebra E N] [Algebra E Θ] [Algebra N Θ] [IsScalarTower E N Θ]
  [IsGalois E N] [IsGalois E Θ] [IsMulCommutative (N ≃ₐ[E] N)] [IsMulCommutative (Θ ≃ₐ[E] Θ)]

private theorem ker_artinSymbol_eq_normRaySubgroup_subcyc {q : ℕ} [NeZero q] {ζ : Θ}
    (hζ : IsPrimitiveRoot ζ q) (htop : (IntermediateField.adjoin E {ζ} : IntermediateField E Θ) = ⊤)
    (𝔣E : Ideal (𝓞 E)) (hq𝔣 : Ideal.span {(q : 𝓞 E)} ∣ 𝔣E)
    (hunr : ∀ v : HeightOneSpectrum (𝓞 E), ¬ v.asIdeal ∣ 𝔣E →
      ((primeAbove E Θ v).under (𝓞 N)).inertia (N ≃ₐ[E] N) = ⊥)
    (hadm : IsAdmissibleModulus E N 𝔣E)
    (hCSb : SecondInequalityCTM E N 𝔣E)
    (hFI : ∀ F : IntermediateField E N, (Module.finrank E F).Prime → FirstInequalityCTM E F 𝔣E) :
    (artinSymbol E N 𝔣E).ker = normRaySubgroup E N 𝔣E := by

  have hP_ker : (narrowRaySubgroup E 𝔣E).subgroupOf (coprimeToModulus E 𝔣E)
      ≤ (artinSymbol E N 𝔣E).ker := by
    intro I hI
    have hI' := Subgroup.mem_subgroupOf.mp hI

    have step : artinSymbol E N 𝔣E
        ⟨(I : (FractionalIdeal ((𝓞 E)⁰) E)ˣ), narrowRaySubgroup_le_coprimeToModulus E 𝔣E hI'⟩ = 1 := by
      refine Subgroup.closure_induction
        (p := fun J hJ =>
          artinSymbol E N 𝔣E ⟨J, narrowRaySubgroup_le_coprimeToModulus E 𝔣E hJ⟩ = 1)
        ?_ (map_one _) (fun J₁ J₂ hJ₁ hJ₂ ih₁ ih₂ => ?_) (fun J hJ ih => ?_) hI'
      · intro J hJgen
        obtain ⟨α, hα0, hα1, hpos, hJα⟩ := (mem_narrowRaySet_iff E).mp hJgen
        exact artinSymbol_sub_eq_one_of_ray E N Θ hζ htop hq𝔣 hunr _ hα0 hα1 hpos hJα
      · show artinSymbol E N 𝔣E
          ⟨J₁ * J₂, narrowRaySubgroup_le_coprimeToModulus E 𝔣E (mul_mem hJ₁ hJ₂)⟩ = 1
        rw [show (⟨J₁ * J₂, _⟩ : ↥(coprimeToModulus E 𝔣E))
            = ⟨J₁, narrowRaySubgroup_le_coprimeToModulus E 𝔣E hJ₁⟩
              * ⟨J₂, narrowRaySubgroup_le_coprimeToModulus E 𝔣E hJ₂⟩ from rfl,
          map_mul, ih₁, ih₂, one_mul]
      · show artinSymbol E N 𝔣E ⟨J⁻¹, narrowRaySubgroup_le_coprimeToModulus E 𝔣E (inv_mem hJ)⟩ = 1
        rw [show (⟨J⁻¹, _⟩ : ↥(coprimeToModulus E 𝔣E))
            = (⟨J, narrowRaySubgroup_le_coprimeToModulus E 𝔣E hJ⟩ : ↥(coprimeToModulus E 𝔣E))⁻¹ from rfl,
          map_inv, ih, inv_one]
    rwa [show (⟨(I : (FractionalIdeal ((𝓞 E)⁰) E)ˣ), _⟩ : ↥(coprimeToModulus E 𝔣E)) = I from rfl,
      ← MonoidHom.mem_ker] at step

  have hfrob := hfrob_of_isAdmissibleModulus E N hadm

  have h := noTotallySplitSub_of_firstInequalityCTM 𝔣E hFI

  exact ker_artinSymbol_eq_normRaySubgroup E N 𝔣E
    (normRaySubgroup_le_ker_artinSymbol E N 𝔣E hP_ker hfrob) h hCSb

end HkerA
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.Deep.NTSupply NumberField IsDedekindDomain"

open scoped nonZeroDivisors

namespace LanglandsTunnell
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

section hcross

set_option maxSynthPendingDepth 3

variable (k E E' : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Field E'] [NumberField E']
  [Algebra k E] [Algebra k E'] [Algebra E E'] [IsScalarTower k E E']

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.HeckeCharacter"

omit [NumberField k] [NumberField E] [NumberField E'] in

private theorem placeUnder'_placeUnder' (w' : HeightOneSpectrum (𝓞 E')) :
    placeUnder' k E' w' = placeUnder' k E (placeUnder' E E' w') :=
  IsDedekindDomain.HeightOneSpectrum.ext
    (by rw [placeUnder'_asIdeal, placeUnder'_asIdeal, placeUnder'_asIdeal, Ideal.under_under])

private theorem fracRelNormUnit_fracRelNormUnit_primeUnit (w' : HeightOneSpectrum (𝓞 E')) :
    fracRelNormUnit k E (fracRelNormUnit E E' (primeUnit E' w'))
      = fracRelNormUnit k E' (primeUnit E' w') := by
  rw [fracRelNormUnit_primeUnit E E' w' (placeUnder' E E' w') (placeUnder'_asIdeal E E' w').symm,
    map_pow,
    fracRelNormUnit_primeUnit k E (placeUnder' E E' w') (placeUnder' k E (placeUnder' E E' w'))
      (placeUnder'_asIdeal k E _).symm,
    fracRelNormUnit_primeUnit k E' w' (placeUnder' k E' w') (placeUnder'_asIdeal k E' w').symm,
    ← pow_mul, placeUnder'_placeUnder' k E E']
  congr 1
  haveI : (placeUnder' k E (placeUnder' E E' w')).asIdeal.IsMaximal :=
    (placeUnder' k E (placeUnder' E E' w')).isMaximal
  haveI : (placeUnder' E E' w').asIdeal.IsMaximal := (placeUnder' E E' w').isMaximal
  haveI : (placeUnder' E E' w').asIdeal.LiesOver (placeUnder' k E (placeUnder' E E' w')).asIdeal :=
    ⟨(placeUnder'_asIdeal k E _).symm⟩
  haveI : w'.asIdeal.LiesOver (placeUnder' E E' w').asIdeal := ⟨(placeUnder'_asIdeal E E' w').symm⟩
  exact (Ideal.inertiaDeg_algebra_tower (placeUnder' k E (placeUnder' E E' w')).asIdeal
    (placeUnder' E E' w').asIdeal w'.asIdeal).symm

end hcross
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section ModulusCast

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.Deep.NTSupply NumberField IsDedekindDomain"

open scoped nonZeroDivisors

variable (F : Type*) [Field F] [NumberField F]

private theorem coe_modulusExt_cast {𝔠₁ 𝔠₂ : Ideal (𝓞 F)} (h : 𝔠₁ = 𝔠₂)
    (B : ↥(coprimeToModulus F 𝔠₁)) :
    ((h ▸ B : ↥(coprimeToModulus F 𝔠₂)) : (FractionalIdeal ((𝓞 F)⁰) F)ˣ)
      = (B : (FractionalIdeal ((𝓞 F)⁰) F)ˣ) := by subst h; rfl

end ModulusCast
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section hcross2

set_option maxSynthPendingDepth 3

variable (k E E' : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Field E'] [NumberField E']
  [Algebra k E] [Algebra k E'] [Algebra E E'] [IsScalarTower k E E']

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.HeckeCharacter"

private theorem fracRelNormUnit_comp (u : (FractionalIdeal ((𝓞 E')⁰) E')ˣ) :
    fracRelNormUnit k E' u = fracRelNormUnit k E (fracRelNormUnit E E' u) := by
  have hmem : u ∈ coprimeToModulus E' ⊤ := fun v hv =>
    absurd (top_le_iff.mp (Ideal.le_of_dvd hv)) v.isPrime.ne_top
  have h := MonoidHom.eq_of_eqOn_dense (closure_primeCarriers_eq_top E' ⊤)
    (f := (fracRelNormUnit k E').comp (coprimeToModulus E' ⊤).subtype)
    (g := ((fracRelNormUnit k E).comp (fracRelNormUnit E E')).comp (coprimeToModulus E' ⊤).subtype)
    (by
      rintro _ ⟨w', _, rfl⟩
      exact (fracRelNormUnit_fracRelNormUnit_primeUnit k E E' w').symm)
  exact DFunLike.congr_fun h ⟨u, hmem⟩

omit [NumberField k] [NumberField E] [NumberField E'] in

private theorem modulusExt_modulusExt (𝔠 : Ideal (𝓞 k)) :
    modulusExt k E' 𝔠 = modulusExt E E' (modulusExt k E 𝔠) := by
  unfold modulusExt
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

end hcross2
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section

set_option autoImplicit false

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.Deep.NTSupply NumberField IsDedekindDomain"

open scoped nonZeroDivisors IsMulCommutative Pointwise

namespace LanglandsTunnell
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.HeckeCharacter"

section PPlus

variable (K E : Type*) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

private theorem relNormCTM_narrowRaySubgroup_subgroupOf_le (𝔣 : Ideal (𝓞 K))
    (I : ↥(coprimeToModulus E (modulusExt K E 𝔣)))
    (hI : I ∈ (narrowRaySubgroup E (modulusExt K E 𝔣)).subgroupOf
      (coprimeToModulus E (modulusExt K E 𝔣))) :
    relNormCTM K E 𝔣 I ∈ (narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣) := by
  have hI' := Subgroup.mem_subgroupOf.mp hI
  have step : (relNormCTM K E 𝔣
      ⟨_, narrowRaySubgroup_le_coprimeToModulus E (modulusExt K E 𝔣) hI'⟩ : ↥(coprimeToModulus K 𝔣)).1
        ∈ narrowRaySubgroup K 𝔣 := by
    refine Subgroup.closure_induction
      (p := fun J hJ => ((relNormCTM K E 𝔣
          ⟨J, narrowRaySubgroup_le_coprimeToModulus E (modulusExt K E 𝔣) hJ⟩).1
        : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) ∈ narrowRaySubgroup K 𝔣)
      ?_ ?_ (fun J₁ J₂ hJ₁ hJ₂ ih₁ ih₂ => ?_) (fun J hJ ih => ?_) hI'
    · intro J hJgen
      obtain ⟨α, hα0, hα1, hpos, hJα⟩ := (mem_narrowRaySet_iff E).mp hJgen
      have heq : (⟨J, narrowRaySubgroup_le_coprimeToModulus E _ (Subgroup.subset_closure hJgen)⟩
            : ↥(coprimeToModulus E (modulusExt K E 𝔣)))
          = ⟨principalUnit E α hα0, principalUnit_mem_coprimeToModulus E hα0 hα1⟩ :=
        Subtype.ext (Units.ext (hJα.trans (principalUnit_val E α hα0).symm))
      show ((relNormCTM K E 𝔣 ⟨J, _⟩).1 : _) ∈ _
      rw [heq]
      refine Subgroup.subset_closure ?_
      rw [mem_narrowRaySet_iff, coe_relNormCTM, Subgroup.coe_mk]
      exact ⟨_, intNorm_ne_zero K E hα0, M4aP2.intNorm_sub_one_mem_of_sub_one_mem K E 𝔣 α hα1,
        M4aP2.intNorm_totPos_of_totPos K E α hα0 hpos,
        (congrArg Units.val (fracRelNormUnit_principalUnit' K E α hα0)).trans
          (principalUnit_val K _ (intNorm_ne_zero K E hα0))⟩
    · show ((relNormCTM K E 𝔣
          ⟨(1 : (FractionalIdeal ((𝓞 E)⁰) E)ˣ), narrowRaySubgroup_le_coprimeToModulus E _ (one_mem _)⟩
          ).1 : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) ∈ narrowRaySubgroup K 𝔣
      rw [show (⟨(1 : (FractionalIdeal ((𝓞 E)⁰) E)ˣ), _⟩ : ↥(coprimeToModulus E _))
          = 1 from rfl, map_one]
      exact one_mem _
    · show ((relNormCTM K E 𝔣 ⟨J₁ * J₂, _⟩).1 : _) ∈ _
      rw [show (⟨J₁ * J₂, _⟩ : ↥(coprimeToModulus E (modulusExt K E 𝔣)))
          = ⟨J₁, narrowRaySubgroup_le_coprimeToModulus E _ hJ₁⟩
            * ⟨J₂, narrowRaySubgroup_le_coprimeToModulus E _ hJ₂⟩ from rfl, map_mul]
      exact mul_mem ih₁ ih₂
    · show ((relNormCTM K E 𝔣 ⟨J⁻¹, _⟩).1 : _) ∈ _
      rw [show (⟨J⁻¹, _⟩ : ↥(coprimeToModulus E (modulusExt K E 𝔣)))
          = (⟨J, narrowRaySubgroup_le_coprimeToModulus E _ hJ⟩ : ↥(coprimeToModulus E _))⁻¹ from rfl,
        map_inv]
      exact inv_mem ih
  rwa [show (⟨(I : (FractionalIdeal ((𝓞 E)⁰) E)ˣ), _⟩ : ↥(coprimeToModulus E _)) = I from rfl,
    ← Subgroup.mem_subgroupOf] at step

end PPlus
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section Range

set_option maxSynthPendingDepth 3

variable (K L E N : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Field E] [NumberField E] [Field N] [NumberField N]
  [Algebra K L] [Algebra K E] [Algebra K N] [Algebra E N] [Algebra L N]
  [IsScalarTower K E N] [IsScalarTower K L N]

private theorem relNormCTM_range_le (𝔣 : Ideal (𝓞 K))
    (I : ↥(coprimeToModulus E (modulusExt K E 𝔣)))
    (hI : I ∈ (relNormCTM E N (modulusExt K E 𝔣)).range) :
    relNormCTM K E 𝔣 I ∈ (relNormCTM K L 𝔣).range := by
  obtain ⟨x, hx⟩ := hI

  refine ⟨relNormCTM L N (modulusExt K L 𝔣) ((modulusExt_modulusExt K L N 𝔣) ▸
    ((modulusExt_modulusExt K E N 𝔣).symm ▸ x)), ?_⟩
  apply Subtype.ext
  rw [coe_relNormCTM, coe_relNormCTM, ← hx, coe_relNormCTM, coe_relNormCTM,
    coe_modulusExt_cast N (modulusExt_modulusExt K L N 𝔣),
    coe_modulusExt_cast N (modulusExt_modulusExt K E N 𝔣).symm,
    ← fracRelNormUnit_comp K L N, ← fracRelNormUnit_comp K E N]

end Range
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section Main

set_option maxSynthPendingDepth 3

variable (K L E N : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Field E] [NumberField E] [Field N] [NumberField N]
  [Algebra K L] [Algebra K E] [Algebra K N] [Algebra E N] [Algebra L N]
  [IsScalarTower K E N] [IsScalarTower K L N]

private theorem relNormCTM_normRaySubgroup_le (𝔣 : Ideal (𝓞 K))
    (I : ↥(coprimeToModulus E (modulusExt K E 𝔣)))
    (hI : I ∈ normRaySubgroup E N (modulusExt K E 𝔣)) :
    relNormCTM K E 𝔣 I ∈ normRaySubgroup K L 𝔣 := by
  unfold normRaySubgroup at hI ⊢
  have key := (Subgroup.map_sup _ _ (relNormCTM K E 𝔣)).symm ▸
    Subgroup.mem_map_of_mem (relNormCTM K E 𝔣) hI
  have hle : Subgroup.map (relNormCTM K E 𝔣)
        ((narrowRaySubgroup E (modulusExt K E 𝔣)).subgroupOf (coprimeToModulus E (modulusExt K E 𝔣)))
      ⊔ Subgroup.map (relNormCTM K E 𝔣) (relNormCTM E N (modulusExt K E 𝔣)).range
      ≤ (narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣) ⊔ (relNormCTM K L 𝔣).range :=
    sup_le_sup
      (fun y hy => by obtain ⟨z, hz, hzy⟩ := hy
                      exact hzy ▸ relNormCTM_narrowRaySubgroup_subgroupOf_le K E 𝔣 z hz)
      (fun y hy => by obtain ⟨z, hz, hzy⟩ := hy
                      exact hzy ▸ relNormCTM_range_le K L E N 𝔣 z hz)
  exact hle key

end Main
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section

set_option autoImplicit false

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.Deep.NTSupply NumberField IsDedekindDomain"

open scoped nonZeroDivisors IsMulCommutative Pointwise

namespace LanglandsTunnell
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.HeckeCharacter"

set_option maxSynthPendingDepth 3

variable (K L E N Θ : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Field E] [NumberField E] [Field N] [NumberField N] [Field Θ] [NumberField Θ]
  [Algebra K L] [Algebra K E] [Algebra K N] [Algebra E N] [Algebra L N]
  [IsScalarTower K E N] [IsScalarTower K L N]
  [Algebra E Θ] [Algebra N Θ] [IsScalarTower E N Θ]
  [IsGalois K L] [IsGalois E N] [IsGalois E Θ]
  [IsMulCommutative (N ≃ₐ[E] N)] [IsMulCommutative (Θ ≃ₐ[E] Θ)]

private theorem hker_family_discharge {q : ℕ} [NeZero q] {ζ : Θ}
    (hζ : IsPrimitiveRoot ζ q) (htop : (IntermediateField.adjoin E {ζ} : IntermediateField E Θ) = ⊤)
    (𝔣 : Ideal (𝓞 K)) (hq𝔣 : Ideal.span {(q : 𝓞 E)} ∣ modulusExt K E 𝔣)
    (hunr : ∀ v : HeightOneSpectrum (𝓞 E), ¬ v.asIdeal ∣ modulusExt K E 𝔣 →
      ((primeAbove E Θ v).under (𝓞 N)).inertia (N ≃ₐ[E] N) = ⊥)
    (hadm : IsAdmissibleModulus E N (modulusExt K E 𝔣))
    (hCSb : SecondInequalityCTM E N (modulusExt K E 𝔣))
    (hFI : ∀ F : IntermediateField E N, (Module.finrank E F).Prime
      → FirstInequalityCTM E F (modulusExt K E 𝔣))
    (hresInj : Function.Injective (resHom K L E N))
    (x : ↥(coprimeToModulus E (modulusExt K E 𝔣)))
    (hx : ((resHom K L E N).comp (artinSymbol E N (modulusExt K E 𝔣))) x = 1) :
    relNormCTM K E 𝔣 x ∈ normRaySubgroup K L 𝔣 := by
  have hx' : artinSymbol E N (modulusExt K E 𝔣) x = 1 := hresInj (by rwa [map_one])
  have hxker : x ∈ normRaySubgroup E N (modulusExt K E 𝔣) := by
    rw [← ker_artinSymbol_eq_normRaySubgroup_subcyc E N Θ hζ htop (modulusExt K E 𝔣) hq𝔣 hunr
      hadm hCSb hFI]
    exact hx'
  exact relNormCTM_normRaySubgroup_le K L E N 𝔣 x hxker

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section

set_option autoImplicit false

namespace LanglandsTunnell
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.HeckeCharacter"

open scoped nonZeroDivisors IsMulCommutative

section Carrier

variable (K : Type*) [Field K] [NumberField K]

@[scoped simp] private theorem coe_ctmInclusion {𝔣 𝔪 : Ideal (𝓞 K)} (h : 𝔣 ∣ 𝔪) (x : ↥(coprimeToModulus K 𝔪)) :
    ((ctmInclusion K h x : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) = (x : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) := rfl

private theorem narrowRaySubgroup_antitone {𝔣 𝔪 : Ideal (𝓞 K)} (h : 𝔣 ∣ 𝔪) : narrowRaySubgroup K 𝔪 ≤ narrowRaySubgroup K 𝔣 := by
  refine Subgroup.closure_mono ?_
  rintro I ⟨α, hα0, hα1, hpos, hI⟩
  exact ⟨α, hα0, Ideal.le_of_dvd h hα1, hpos, hI⟩

end Carrier
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section Norm

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] in

private theorem modulusExt_dvd_modulusExt {𝔣 𝔪 : Ideal (𝓞 K)} (h : 𝔣 ∣ 𝔪) : modulusExt K L 𝔣 ∣ modulusExt K L 𝔪 :=
  Ideal.le_of_dvd h |> Ideal.map_mono |> Ideal.dvd_iff_le.mpr

private theorem relNormCTM_ctmInclusion {𝔣 𝔪 : Ideal (𝓞 K)} (h : 𝔣 ∣ 𝔪) (y : ↥(coprimeToModulus L (modulusExt K L 𝔪))) :
    relNormCTM K L 𝔣 (ctmInclusion L (modulusExt_dvd_modulusExt K L h) y) = ctmInclusion K h (relNormCTM K L 𝔪 y) :=
  Subtype.ext rfl

private theorem map_normRaySubgroup_ctmInclusion_le {𝔣 𝔪 : Ideal (𝓞 K)} (h : 𝔣 ∣ 𝔪) :
    (normRaySubgroup K L 𝔪).map (ctmInclusion K h) ≤ normRaySubgroup K L 𝔣 := by
  rw [normRaySubgroup, normRaySubgroup, Subgroup.map_sup]
  refine sup_le_sup ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact narrowRaySubgroup_antitone K h (Subgroup.mem_subgroupOf.mp hx)
  · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨ctmInclusion L (modulusExt_dvd_modulusExt K L h) y, relNormCTM_ctmInclusion K L h y⟩

private theorem ctmInclusion_mem_normRaySubgroup {𝔣 𝔪 : Ideal (𝓞 K)} (h : 𝔣 ∣ 𝔪) {x : ↥(coprimeToModulus K 𝔪)}
    (hx : x ∈ normRaySubgroup K L 𝔪) : ctmInclusion K h x ∈ normRaySubgroup K L 𝔣 :=
  map_normRaySubgroup_ctmInclusion_le K L h ⟨x, hx, rfl⟩

end Norm
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

section

set_option autoImplicit false

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.Deep.NTSupply NumberField IsDedekindDomain"

open scoped nonZeroDivisors IsMulCommutative Pointwise

namespace LanglandsTunnell
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.HeckeCharacter"

section PerICore

set_option maxSynthPendingDepth 3

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] {𝔣 : Ideal (𝓞 K)} {i : ↥(primeCarriers K 𝔣)}
  (c : ArtinFieldCore K L 𝔣 i)

private theorem hker_of_core (hCSb : SecondInequalityCTM c.E c.N (modulusExt K c.E c.𝔪))
    (hFI : ∀ F : IntermediateField c.E c.N, (Module.finrank c.E F).Prime
      → FirstInequalityCTM c.E F (modulusExt K c.E c.𝔪))
    (x : c.Ip) (hx : c.ωpi x = 1) : c.Ni x ∈ normRaySubgroup K L 𝔣 :=
  ctmInclusion_mem_normRaySubgroup K L c.h𝔪
    (hker_family_discharge K L c.E c.N c.Θ c.hζ c.htop c.𝔪 c.hq𝔪 c.hunr c.hadm hCSb hFI c.hresInj x hx)

end PerICore
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.M4aP2"

set_option autoImplicit false
p2m_open "NumberField HeckeCharacter P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.HeckeCharacter LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.LanglandsTunnell.P2.Artin"

theorem solution
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] {𝔣 : Ideal (𝓞 K)} {i : ↥(primeCarriers K 𝔣)}
    (c : ArtinFieldCore K L 𝔣 i)
    (hCSb : SecondInequalityCTM c.E c.N (modulusExt K c.E c.𝔪))
    (hFI : ∀ F : IntermediateField c.E c.N, (Module.finrank c.E F).Prime
      → FirstInequalityCTM c.E F (modulusExt K c.E c.𝔪))
    (x : c.Ip) (hx : c.ωpi x = 1) : c.Ni x ∈ normRaySubgroup K L 𝔣 := by
  exact LanglandsTunnell.P2.Artin.hker_of_core c hCSb hFI x hx

end S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one
end P2MW
export P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one (solution)
