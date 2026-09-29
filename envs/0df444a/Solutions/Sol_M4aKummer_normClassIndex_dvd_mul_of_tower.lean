-- Prove2me | solution 1 for M4aKummer.normClassIndex_dvd_mul_of_tower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/0990aa39-39d9-575e-a568-251c48c6ece9

import Definitions.Def_NarrowRayClassGroup
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.NumberTheory.NumberField.Norm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aKummer_normClassIndex_dvd_mul_of_tower

set_option Elab.async false
set_option autoImplicit false
set_option maxSynthPendingDepth 3

open NumberField

section SegIndex

namespace M4aKummer
namespace SolH3
namespace Index

open Subgroup

variable {G A B C : Type*} [CommGroup G] [CommGroup A] [CommGroup B] [CommGroup C]

theorem index_map_quotientMk_of_le {P H : Subgroup G} (hPH : P ≤ H) :
    (H.map (QuotientGroup.mk' P)).index = H.index :=
  index_map_eq H (QuotientGroup.mk'_surjective P)
    (by rw [QuotientGroup.ker_mk']; exact hPH)

theorem range_comp_eq_map_range (f : B →* A) (g : C →* B) :
    (f.comp g).range = g.range.map f := by
  ext y
  constructor
  · rintro ⟨c, rfl⟩
    exact mem_map.mpr ⟨g c, ⟨c, rfl⟩, rfl⟩
  · intro hy
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c, rfl⟩

theorem relIndex_map_range_dvd (f : B →* A) (V : Subgroup B) :
    (V.map f).relIndex f.range ∣ V.index := by
  rw [MonoidHom.range_eq_map, ← relIndex_comap, relIndex_top_right]
  exact index_dvd_of_le ((gc_map_comap f).le_u_l V)

theorem index_map_dvd_mul (f : B →* A) (V : Subgroup B) :
    (V.map f).index ∣ V.index * f.range.index := by
  have hle : V.map f ≤ f.range := by
    rw [MonoidHom.range_eq_map]
    exact map_mono le_top
  rw [← relIndex_mul_index hle]
  exact mul_dvd_mul_right (relIndex_map_range_dvd f V) f.range.index

theorem index_map_quotientMk_sup (P H : Subgroup A) :
    (H.map (QuotientGroup.mk' P)).index = (P ⊔ H).index := by
  have hmap : (P ⊔ H).map (QuotientGroup.mk' P) = H.map (QuotientGroup.mk' P) := by
    rw [Subgroup.map_sup]
    have hP : P.map (QuotientGroup.mk' P) = ⊥ := by
      rw [eq_bot_iff]
      rintro x hx
      obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
      exact mem_bot.mpr ((QuotientGroup.eq_one_iff y).mpr hy)
    rw [hP, bot_sup_eq]
  rw [← hmap, index_map_quotientMk_of_le le_sup_left]

theorem index_sup_map_dvd_mul (φ : C →* A) (P : Subgroup A) (B : Subgroup C) :
    (P ⊔ B.map φ).index ∣ B.index * (P ⊔ φ.range).index := by
  have hcompR : ((QuotientGroup.mk' P).comp φ).range.index = (P ⊔ φ.range).index := by
    rw [range_comp_eq_map_range, index_map_quotientMk_sup]
  have hmapB : B.map ((QuotientGroup.mk' P).comp φ) =
      (B.map φ).map (QuotientGroup.mk' P) := by
    rw [map_map]
  have h := index_map_dvd_mul ((QuotientGroup.mk' P).comp φ) B
  rw [hmapB, index_map_quotientMk_sup, hcompR] at h
  exact h

end M4aKummer.SolH3.Index

end SegIndex

section SegT2

namespace M4aKummer
namespace SolH3
namespace T2

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

theorem intNorm_sub_one_mem_of_sub_one_mem (𝔠 : Ideal (𝓞 k)) (y : 𝓞 E)
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

theorem intNorm_totPos_of_totPos (y : 𝓞 E) (hy0 : y ≠ 0)
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

end M4aKummer.SolH3.T2
p2m_reactivate "P2MW.S_M4aKummer_normClassIndex_dvd_mul_of_tower.M4aKummer P2MW.S_M4aKummer_normClassIndex_dvd_mul_of_tower.M4aKummer.SolH3 P2MW.S_M4aKummer_normClassIndex_dvd_mul_of_tower.M4aKummer.SolH3.T2"
p2m_reactivate "P2MW.S_M4aKummer_normClassIndex_dvd_mul_of_tower.M4aKummer P2MW.S_M4aKummer_normClassIndex_dvd_mul_of_tower.M4aKummer.SolH3"
p2m_reactivate "P2MW.S_M4aKummer_normClassIndex_dvd_mul_of_tower.M4aKummer"

end SegT2
p2m_reactivate "P2MW.S_M4aKummer_normClassIndex_dvd_mul_of_tower.M4aKummer P2MW.S_M4aKummer_normClassIndex_dvd_mul_of_tower.M4aKummer.SolH3 P2MW.S_M4aKummer_normClassIndex_dvd_mul_of_tower.M4aKummer.SolH3.T2"

noncomputable section SegNorm

open IsDedekindDomain Deep.NTSupply
open scoped nonZeroDivisors

namespace M4aKummer
namespace SolH3

section TwoFields

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

abbrev nrm : (FractionalIdeal ((𝓞 E)⁰) E)ˣ →* (FractionalIdeal ((𝓞 k)⁰) k)ˣ :=
  raySymbolUnitsHom E (fun w : HeightOneSpectrum (𝓞 E) =>
    primeUnit k (w.under (𝓞 k)) ^ ((w.under (𝓞 k)).asIdeal.inertiaDeg' w.asIdeal))

theorem nrm_primeUnit (w : HeightOneSpectrum (𝓞 E)) :
    nrm k E (primeUnit E w) = primeUnit k (w.under (𝓞 k)) ^ ((w.under (𝓞 k)).asIdeal.inertiaDeg' w.asIdeal) := by
  show raySymbol E _ ((primeUnit E w : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) : FractionalIdeal ((𝓞 E)⁰) E) = _
  rw [raySymbol_primeUnit]

omit [NumberField k] in

theorem val_finprod {ι α : Type*} [CommMonoid α] (f : ι → αˣ) (hf : Function.HasFiniteMulSupport f) :
    (((∏ᶠ i, f i : αˣ)) : α) = ∏ᶠ i, (f i : α) :=
  MonoidHom.map_finprod (Units.coeHom α) hf

theorem finprod_primeUnit_zpow_count (I : (FractionalIdeal ((𝓞 k)⁰) k)ˣ) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 k),
        primeUnit k v ^ FractionalIdeal.count k v (I : FractionalIdeal ((𝓞 k)⁰) k) = I := by
  apply Units.ext
  rw [val_finprod _ (hasFiniteMulSupport_raySymbol_factors k (primeUnit k) _)]
  simp only [Units.val_zpow_eq_zpow_val, primeUnit_val]
  exact FractionalIdeal.finprod_heightOneSpectrum_factorization' k I.ne_zero

theorem hom_eq_raySymbolUnitsHom {G : Type*} [CommGroup G] (ψ : (FractionalIdeal ((𝓞 k)⁰) k)ˣ →* G) :
    ψ = raySymbolUnitsHom k (fun v => ψ (primeUnit k v)) := by
  refine MonoidHom.ext fun I => ?_
  conv_lhs => rw [← finprod_primeUnit_zpow_count k I]
  rw [MonoidHom.map_finprod ψ (hasFiniteMulSupport_raySymbol_factors k (primeUnit k) _)]
  simp only [map_zpow]
  rfl

theorem nrm_mem_coprimeToModulus {𝔠 : Ideal (𝓞 k)} {Y : (FractionalIdeal ((𝓞 E)⁰) E)ˣ}
    (hY : Y ∈ coprimeToModulus E (𝔠.map (algebraMap (𝓞 k) (𝓞 E)))) :
    nrm k E Y ∈ coprimeToModulus k 𝔠 := by
  refine (mem_coprimeToModulus_iff k).mpr fun v hv => ?_
  show FractionalIdeal.count k v ((raySymbol E _ (Y : FractionalIdeal ((𝓞 E)⁰) E) :
    (FractionalIdeal ((𝓞 k)⁰) k)ˣ) : FractionalIdeal ((𝓞 k)⁰) k) = 0
  unfold raySymbol
  rw [val_finprod _ (hasFiniteMulSupport_raySymbol_factors E _ _)]
  refine finprod_induction (fun I : FractionalIdeal ((𝓞 k)⁰) k => FractionalIdeal.count k v I = 0)
    (FractionalIdeal.count_one k v) (fun I J hI hJ => ?_) (fun w => ?_)
  · by_cases hI0 : I = 0
    · rw [hI0, zero_mul]; exact FractionalIdeal.count_zero k v
    by_cases hJ0 : J = 0
    · rw [hJ0, mul_zero]; exact FractionalIdeal.count_zero k v
    rw [FractionalIdeal.count_mul k v hI0 hJ0, hI, hJ, add_zero]
  · rw [Units.val_zpow_eq_zpow_val, FractionalIdeal.count_zpow, Units.val_pow_eq_pow_val,
      FractionalIdeal.count_pow, primeUnit_val]
    by_cases hw : w.under (𝓞 k) = v
    · have hw' : w.asIdeal ∣ 𝔠.map (algebraMap (𝓞 k) (𝓞 E)) := by
        rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
        have h := Ideal.le_of_dvd hv
        rw [← hw] at h
        exact h
      rw [(mem_coprimeToModulus_iff E).mp hY w hw', zero_mul]
    · rw [FractionalIdeal.count_maximal_coprime k v hw, mul_zero, mul_zero]

theorem relNorm_mem_nzd {I : Ideal (𝓞 E)} (hI : I ∈ (nonZeroDivisors (Ideal (𝓞 E)))) :
    Ideal.relNorm (𝓞 k) I ∈ nonZeroDivisors (Ideal (𝓞 k)) :=
  mem_nonZeroDivisors_of_ne_zero (fun h =>
    (mem_nonZeroDivisors_iff_ne_zero.mp hI) (by
      rw [Submodule.zero_eq_bot] at *; exact Ideal.relNorm_eq_bot_iff.mp h))

theorem nrm_primeUnit_eq_relNorm (w : HeightOneSpectrum (𝓞 E)) :
    nrm k E (primeUnit E w)
      = FractionalIdeal.mk0 k ⟨Ideal.relNorm (𝓞 k) w.asIdeal, relNorm_mem_nzd k E
          (mem_nonZeroDivisors_of_ne_zero (by
            rw [Ne, Submodule.zero_eq_bot]; exact w.ne_bot))⟩ := by
  haveI : PerfectField (FractionRing (𝓞 k)) := PerfectField.ofCharZero
  haveI : w.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal w.isPrime w.ne_bot
  haveI : (w.under (𝓞 k)).asIdeal.IsMaximal :=
    Ideal.IsPrime.isMaximal (w.under (𝓞 k)).isPrime (w.under (𝓞 k)).ne_bot
  haveI : w.asIdeal.LiesOver (w.under (𝓞 k)).asIdeal := ⟨rfl⟩
  rw [nrm_primeUnit k E w]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, primeUnit_val, FractionalIdeal.coe_mk0, ← FractionalIdeal.coeIdeal_pow]
  rw [Ideal.inertiaDeg'_eq_inertiaDeg]
  exact congrArg _ (Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 k)).asIdeal).symm

theorem nrm_mk0 (I : (Ideal (𝓞 E))⁰) :
    ((nrm k E (FractionalIdeal.mk0 E I) :
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
      map_mul, map_mul (nrm k E), Units.val_mul, hpw,
      nrm_primeUnit_eq_relNorm k E w, FractionalIdeal.coe_mk0,
      ih ha_nz ha', map_mul (Ideal.relNorm (𝓞 k)), FractionalIdeal.coeIdeal_mul]

theorem intNorm_ne_zero {α : 𝓞 E} (hα : α ≠ 0) : Algebra.intNorm (𝓞 k) (𝓞 E) α ≠ 0 := by
  intro h
  have : Ideal.relNorm (𝓞 k) (Ideal.span {α}) = (⊥ : Ideal (𝓞 k)) := by
    rw [Ideal.relNorm_singleton, h, Ideal.span_singleton_eq_bot]
  exact hα (Ideal.span_singleton_eq_bot.mp (Ideal.relNorm_eq_bot_iff.mp this))

theorem nrm_principalUnit (α : 𝓞 E) (hα : α ≠ 0) :
    nrm k E (principalUnit E α hα)
      = principalUnit k (Algebra.intNorm (𝓞 k) (𝓞 E) α) (intNorm_ne_zero k E hα) := by
  apply Units.ext
  rw [show principalUnit E α hα = FractionalIdeal.mk0 E ⟨Ideal.span {α}, _⟩ from rfl,
    nrm_mk0 k E, Ideal.relNorm_singleton, principalUnit_val]

def nrmCTM (𝔠 : Ideal (𝓞 k)) :
    ↥(coprimeToModulus E (𝔠.map (algebraMap (𝓞 k) (𝓞 E)))) →* ↥(coprimeToModulus k 𝔠) :=
  ((nrm k E).comp (coprimeToModulus E (𝔠.map (algebraMap (𝓞 k) (𝓞 E)))).subtype).codRestrict
    (coprimeToModulus k 𝔠) (fun Y => nrm_mem_coprimeToModulus k E Y.2)

theorem coe_nrmCTM {𝔠 : Ideal (𝓞 k)} (Y : ↥(coprimeToModulus E (𝔠.map (algebraMap (𝓞 k) (𝓞 E))))) :
    ((nrmCTM k E 𝔠 Y : ↥(coprimeToModulus k 𝔠)) : (FractionalIdeal ((𝓞 k)⁰) k)ˣ)
      = nrm k E (Y : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) := rfl

theorem normSub_eq_range (𝔠 : Ideal (𝓞 k)) :
    ((coprimeToModulus E (𝔠.map (algebraMap (𝓞 k) (𝓞 E)))).map
        (raySymbolUnitsHom E (fun w : HeightOneSpectrum (𝓞 E) =>
          primeUnit k (w.under (𝓞 k)) ^ ((w.under (𝓞 k)).asIdeal.inertiaDeg' w.asIdeal)))).subgroupOf
        (coprimeToModulus k 𝔠)
      = (nrmCTM k E 𝔠).range := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  · rintro ⟨Y, hY, hYx⟩
    exact ⟨⟨Y, hY⟩, Subtype.ext hYx⟩
  · rintro ⟨Y, rfl⟩
    exact ⟨Y, Y.2, rfl⟩

theorem map_narrowRaySubgroup_le (𝔣 : Ideal (𝓞 k)) :
    (narrowRaySubgroup E (𝔣.map (algebraMap (𝓞 k) (𝓞 E)))).map (nrm k E) ≤ narrowRaySubgroup k 𝔣 := by
  show (Subgroup.closure _).map _ ≤ Subgroup.closure _
  rw [MonoidHom.map_closure]
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨I, hI, rfl⟩
  obtain ⟨α, hα0, hα1, hpos, hIα⟩ := hI
  have hI' : I = principalUnit E α hα0 := Units.ext (hIα.trans (principalUnit_val E α hα0).symm)
  rw [hI', nrm_principalUnit]
  exact Subgroup.subset_closure ⟨Algebra.intNorm (𝓞 k) (𝓞 E) α, intNorm_ne_zero k E hα0,
    T2.intNorm_sub_one_mem_of_sub_one_mem k E 𝔣 α hα1, T2.intNorm_totPos_of_totPos k E α hα0 hpos,
    principalUnit_val k _ _⟩

theorem map_nrmCTM_narrowRaySubgroupOf_le (𝔣 : Ideal (𝓞 k)) :
    ((narrowRaySubgroup E (𝔣.map (algebraMap (𝓞 k) (𝓞 E)))).subgroupOf
        (coprimeToModulus E (𝔣.map (algebraMap (𝓞 k) (𝓞 E))))).map (nrmCTM k E 𝔣)
      ≤ (narrowRaySubgroup k 𝔣).subgroupOf (coprimeToModulus k 𝔣) := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : ((x : ↥(coprimeToModulus E (𝔣.map (algebraMap (𝓞 k) (𝓞 E))))) :
      (FractionalIdeal ((𝓞 E)⁰) E)ˣ) ∈ narrowRaySubgroup E (𝔣.map (algebraMap (𝓞 k) (𝓞 E))) :=
    Subgroup.mem_subgroupOf.mp hx
  refine Subgroup.mem_subgroupOf.mpr ?_
  rw [coe_nrmCTM]
  exact map_narrowRaySubgroup_le k E 𝔣 ⟨_, hx', rfl⟩

end TwoFields
p2m_reactivate "P2MW.S_M4aKummer_normClassIndex_dvd_mul_of_tower.M4aKummer P2MW.S_M4aKummer_normClassIndex_dvd_mul_of_tower.M4aKummer.SolH3 P2MW.S_M4aKummer_normClassIndex_dvd_mul_of_tower.M4aKummer.SolH3.T2"

section Tower

variable (k M E : Type*) [Field k] [NumberField k] [Field M] [NumberField M] [Field E] [NumberField E]
  [Algebra k M] [Algebra M E] [Algebra k E] [IsScalarTower k M E]

omit [NumberField k] [NumberField M] [NumberField E] in

theorem under_under_eq (w : HeightOneSpectrum (𝓞 E)) :
    w.under (𝓞 k) = (w.under (𝓞 M)).under (𝓞 k) :=
  HeightOneSpectrum.ext (by
    simp only [HeightOneSpectrum.under_asIdeal]
    rw [Ideal.under_under])

theorem nrm_comp : (nrm k M).comp (nrm M E) = nrm k E := by
  rw [hom_eq_raySymbolUnitsHom E ((nrm k M).comp (nrm M E))]
  show raySymbolUnitsHom E _ = raySymbolUnitsHom E _
  congr 1
  funext w
  rw [MonoidHom.comp_apply, nrm_primeUnit M E w, map_pow, nrm_primeUnit k M, ← pow_mul, under_under_eq k M E w]
  congr 1
  haveI := ((w.under (𝓞 M)).under (𝓞 k)).isMaximal
  haveI := (w.under (𝓞 M)).isMaximal
  haveI : (w.under (𝓞 M)).asIdeal.LiesOver ((w.under (𝓞 M)).under (𝓞 k)).asIdeal := ⟨rfl⟩
  haveI : w.asIdeal.LiesOver (w.under (𝓞 M)).asIdeal := ⟨rfl⟩
  exact (Ideal.inertiaDeg_algebra_tower ((w.under (𝓞 M)).under (𝓞 k)).asIdeal (w.under (𝓞 M)).asIdeal
    w.asIdeal).symm

theorem range_nrmCTM_comp (𝔣 : Ideal (𝓞 k)) :
    ((nrmCTM k M 𝔣).comp (nrmCTM M E (𝔣.map (algebraMap (𝓞 k) (𝓞 M))))).range
      = (nrmCTM k E 𝔣).range := by
  have hmod : (𝔣.map (algebraMap (𝓞 k) (𝓞 M))).map (algebraMap (𝓞 M) (𝓞 E))
      = 𝔣.map (algebraMap (𝓞 k) (𝓞 E)) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hval : ∀ u : (FractionalIdeal ((𝓞 E)⁰) E)ˣ, nrm k M (nrm M E u) = nrm k E u := fun u =>
    DFunLike.congr_fun (nrm_comp k M E) u
  ext x
  simp only [MonoidHom.mem_range, MonoidHom.comp_apply]
  constructor
  · rintro ⟨Y, rfl⟩
    refine ⟨⟨(Y : (FractionalIdeal ((𝓞 E)⁰) E)ˣ), hmod ▸ Y.2⟩, Subtype.ext ?_⟩
    rw [coe_nrmCTM, coe_nrmCTM, coe_nrmCTM, hval]
  · rintro ⟨Y, rfl⟩
    refine ⟨⟨(Y : (FractionalIdeal ((𝓞 E)⁰) E)ˣ), hmod.symm ▸ Y.2⟩, Subtype.ext ?_⟩
    rw [coe_nrmCTM, coe_nrmCTM, coe_nrmCTM, hval]

theorem main (𝔣 : Ideal (𝓞 k)) :
    ((narrowRaySubgroup k 𝔣).subgroupOf (coprimeToModulus k 𝔣) ⊔ (nrmCTM k E 𝔣).range).index ∣
      ((narrowRaySubgroup k 𝔣).subgroupOf (coprimeToModulus k 𝔣) ⊔ (nrmCTM k M 𝔣).range).index *
        ((narrowRaySubgroup M (𝔣.map (algebraMap (𝓞 k) (𝓞 M)))).subgroupOf
            (coprimeToModulus M (𝔣.map (algebraMap (𝓞 k) (𝓞 M)))) ⊔
          (nrmCTM M E (𝔣.map (algebraMap (𝓞 k) (𝓞 M)))).range).index := by
  have hB : (narrowRaySubgroup k 𝔣).subgroupOf (coprimeToModulus k 𝔣) ⊔
      ((narrowRaySubgroup M (𝔣.map (algebraMap (𝓞 k) (𝓞 M)))).subgroupOf
          (coprimeToModulus M (𝔣.map (algebraMap (𝓞 k) (𝓞 M)))) ⊔
        (nrmCTM M E (𝔣.map (algebraMap (𝓞 k) (𝓞 M)))).range).map (nrmCTM k M 𝔣)
      = (narrowRaySubgroup k 𝔣).subgroupOf (coprimeToModulus k 𝔣) ⊔ (nrmCTM k E 𝔣).range := by
    rw [Subgroup.map_sup, ← sup_assoc, sup_eq_left.mpr (map_nrmCTM_narrowRaySubgroupOf_le k M 𝔣),
      MonoidHom.map_range, range_nrmCTM_comp k M E 𝔣]
  have key := Index.index_sup_map_dvd_mul (nrmCTM k M 𝔣)
    ((narrowRaySubgroup k 𝔣).subgroupOf (coprimeToModulus k 𝔣))
    ((narrowRaySubgroup M (𝔣.map (algebraMap (𝓞 k) (𝓞 M)))).subgroupOf
        (coprimeToModulus M (𝔣.map (algebraMap (𝓞 k) (𝓞 M)))) ⊔
      (nrmCTM M E (𝔣.map (algebraMap (𝓞 k) (𝓞 M)))).range)
  rw [hB] at key
  rw [mul_comm]
  exact key

end Tower
p2m_reactivate "P2MW.S_M4aKummer_normClassIndex_dvd_mul_of_tower.M4aKummer P2MW.S_M4aKummer_normClassIndex_dvd_mul_of_tower.M4aKummer.SolH3 P2MW.S_M4aKummer_normClassIndex_dvd_mul_of_tower.M4aKummer.SolH3.T2"

end M4aKummer.SolH3
p2m_reactivate "P2MW.S_M4aKummer_normClassIndex_dvd_mul_of_tower.M4aKummer P2MW.S_M4aKummer_normClassIndex_dvd_mul_of_tower.M4aKummer.SolH3 P2MW.S_M4aKummer_normClassIndex_dvd_mul_of_tower.M4aKummer.SolH3.T2"
p2m_reactivate "P2MW.S_M4aKummer_normClassIndex_dvd_mul_of_tower.M4aKummer P2MW.S_M4aKummer_normClassIndex_dvd_mul_of_tower.M4aKummer.SolH3 P2MW.S_M4aKummer_normClassIndex_dvd_mul_of_tower.M4aKummer.SolH3.T2"

end SegNorm
p2m_reactivate "P2MW.S_M4aKummer_normClassIndex_dvd_mul_of_tower.M4aKummer P2MW.S_M4aKummer_normClassIndex_dvd_mul_of_tower.M4aKummer.SolH3 P2MW.S_M4aKummer_normClassIndex_dvd_mul_of_tower.M4aKummer.SolH3.T2"

open NumberField IsDedekindDomain Deep.NTSupply

theorem solution
    (k M E : Type*) [Field k] [NumberField k] [Field M] [NumberField M] [Field E] [NumberField E]
    [Algebra k M] [Algebra M E] [Algebra k E] [IsScalarTower k M E] (𝔣 : Ideal (𝓞 k)) :
    ((narrowRaySubgroup k 𝔣).subgroupOf (coprimeToModulus k 𝔣) ⊔
      ((coprimeToModulus E (𝔣.map (algebraMap (𝓞 k) (𝓞 E)))).map
        (raySymbolUnitsHom E (fun w : HeightOneSpectrum (𝓞 E) =>
          primeUnit k (w.under (𝓞 k)) ^ ((w.under (𝓞 k)).asIdeal.inertiaDeg' w.asIdeal)))).subgroupOf
        (coprimeToModulus k 𝔣)).index
    ∣ ((narrowRaySubgroup k 𝔣).subgroupOf (coprimeToModulus k 𝔣) ⊔
        ((coprimeToModulus M (𝔣.map (algebraMap (𝓞 k) (𝓞 M)))).map
          (raySymbolUnitsHom M (fun u : HeightOneSpectrum (𝓞 M) =>
            primeUnit k (u.under (𝓞 k)) ^ ((u.under (𝓞 k)).asIdeal.inertiaDeg' u.asIdeal)))).subgroupOf
          (coprimeToModulus k 𝔣)).index
      * ((narrowRaySubgroup M (𝔣.map (algebraMap (𝓞 k) (𝓞 M)))).subgroupOf
            (coprimeToModulus M (𝔣.map (algebraMap (𝓞 k) (𝓞 M)))) ⊔
          ((coprimeToModulus E ((𝔣.map (algebraMap (𝓞 k) (𝓞 M))).map (algebraMap (𝓞 M) (𝓞 E)))).map
            (raySymbolUnitsHom E (fun w : HeightOneSpectrum (𝓞 E) =>
              primeUnit M (w.under (𝓞 M)) ^ ((w.under (𝓞 M)).asIdeal.inertiaDeg' w.asIdeal)))).subgroupOf
            (coprimeToModulus M (𝔣.map (algebraMap (𝓞 k) (𝓞 M))))).index := by
  rw [M4aKummer.SolH3.normSub_eq_range k E 𝔣, M4aKummer.SolH3.normSub_eq_range k M 𝔣,
    M4aKummer.SolH3.normSub_eq_range M E (𝔣.map (algebraMap (𝓞 k) (𝓞 M)))]
  exact M4aKummer.SolH3.main k M E 𝔣

#print axioms solution

end S_M4aKummer_normClassIndex_dvd_mul_of_tower
end P2MW
export P2MW.S_M4aKummer_normClassIndex_dvd_mul_of_tower (solution)
