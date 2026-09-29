-- Prove2me | solution 1 for NumberField.TateGlobal.exists_forall_finite_and_card_le_of_archLocalChar_eq_cpow_const_of_pairwise_ne_normOneIdeles
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/3a17fd6a-2275-5b29-a073-7148c48b5d89

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_NumberField_IdeleBox
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_AdeleRing_finiteIndex_principalIdeles_sup_unitIdelesOutside
import Theorems.Thm_NumberField_TateGlobal_apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_forall_finite_and_card_le_of_archLocalChar_eq_cpow_const_of_pairwise_ne_normOneIdeles
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

noncomputable section

open NumberField NumberField.TateGlobal NumberField.AdeleRing NumberField.AdelicLevel IsDedekindDomain M4aHerbrand
open AutomorphicForm

namespace C3cAux

variable {K : Type} [Field K] [NumberField K]

def archPart (x : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K)ˣ where
  val := ((x : AdeleRing (𝓞 K) K).1, 1)
  inv := (((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1, 1)
  val_inv := by
    refine Prod.ext ?_ (one_mul 1)
    show (x : AdeleRing (𝓞 K) K).1 * ((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1
    have h : ((x * x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = 1 := by
      rw [mul_inv_cancel, Units.val_one]
    have h' : ((x : AdeleRing (𝓞 K) K) * ((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 =
        (1 : AdeleRing (𝓞 K) K).1 := congrArg Prod.fst h
    exact h'
  inv_val := by
    refine Prod.ext ?_ (one_mul 1)
    show ((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 * (x : AdeleRing (𝓞 K) K).1 = 1
    have h : ((x⁻¹ * x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = 1 := by
      rw [inv_mul_cancel, Units.val_one]
    have h' : (((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (x : AdeleRing (𝓞 K) K)).1 =
        (1 : AdeleRing (𝓞 K) K).1 := congrArg Prod.fst h
    exact h'

def finPart (x : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K)ˣ where
  val := (1, (x : AdeleRing (𝓞 K) K).2)
  inv := (1, ((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2)
  val_inv := by
    refine Prod.ext (one_mul 1) ?_
    show (x : AdeleRing (𝓞 K) K).2 * ((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = 1
    have h : ((x * x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = 1 := by
      rw [mul_inv_cancel, Units.val_one]
    have h' : ((x : AdeleRing (𝓞 K) K) * ((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 =
        (1 : AdeleRing (𝓞 K) K).2 := congrArg Prod.snd h
    exact h'
  inv_val := by
    refine Prod.ext (one_mul 1) ?_
    show ((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 * (x : AdeleRing (𝓞 K) K).2 = 1
    have h : ((x⁻¹ * x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = 1 := by
      rw [inv_mul_cancel, Units.val_one]
    have h' : (((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (x : AdeleRing (𝓞 K) K)).2 =
        (1 : AdeleRing (𝓞 K) K).2 := congrArg Prod.snd h
    exact h'

theorem archPart_val (x : (AdeleRing (𝓞 K) K)ˣ) :
    ((archPart x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = ((x : AdeleRing (𝓞 K) K).1, 1) := rfl

theorem finPart_val (x : (AdeleRing (𝓞 K) K)ˣ) :
    ((finPart x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = (1, (x : AdeleRing (𝓞 K) K).2) := rfl

theorem archPart_mul_finPart (x : (AdeleRing (𝓞 K) K)ˣ) : archPart x * finPart x = x :=
  Units.ext (Prod.ext (mul_one _) (one_mul _))

theorem finitePartUnits_finPart (x : (AdeleRing (𝓞 K) K)ˣ) :
    finitePartUnits (𝓞 K) K (finPart x) = finitePartUnits (𝓞 K) K x :=
  Units.ext rfl

theorem archPart_eq_prod (x : (AdeleRing (𝓞 K) K)ˣ) :
    archPart x = ∏ w : InfinitePlace K, archUnitHom w (infiniteUnitsComponent (𝓞 K) K w x) := by
  classical
  apply Units.ext
  rw [Units.coe_prod, archPart_val]
  set g : InfinitePlace K → AdeleRing (𝓞 K) K :=
    fun w => ((archUnitHom w (infiniteUnitsComponent (𝓞 K) K w x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)
    with hg
  have hg1 : ∀ w v, (g w).1 v = Function.update (1 : InfiniteAdeleRing K) w
      ((infiniteUnitsComponent (𝓞 K) K w x : (w.Completion)ˣ) : w.Completion) v := fun _ _ => rfl
  have hg2 : ∀ w, (g w).2 = 1 := fun _ => rfl
  refine Prod.ext ?_ ?_
  ·
    funext v
    have h1 : (∏ w : InfinitePlace K, g w).1 v = ∏ w : InfinitePlace K, (g w).1 v := by
      have := map_prod ((archEval K v).comp (adeleArch (𝓞 K) K)) g Finset.univ
      exact this
    show (x : AdeleRing (𝓞 K) K).1 v = (∏ w : InfinitePlace K, g w).1 v
    rw [h1]
    simp only [hg1]
    rw [Finset.prod_eq_single v]
    · rw [Function.update_self, val_infiniteUnitsComponent]
    · intro w _ hw
      rw [Function.update_of_ne (Ne.symm hw)]
      rfl
    · intro h; exact absurd (Finset.mem_univ v) h
  · have h2 : (∏ w : InfinitePlace K, g w).2 = ∏ w : InfinitePlace K, (g w).2 := by
      have := map_prod (adeleFin (𝓞 K) K) g Finset.univ
      exact this
    show (1 : FiniteAdeleRing (𝓞 K) K) = (∏ w : InfinitePlace K, g w).2
    rw [h2]
    simp only [hg2, Finset.prod_const_one]

theorem map_archPart_eq_prod (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (x : (AdeleRing (𝓞 K) K)ˣ) :
    χ (archPart x) = ∏ w : InfinitePlace K, archLocalChar χ w (infiniteUnitsComponent (𝓞 K) K w x) := by
  rw [archPart_eq_prod, map_prod]
  rfl

theorem ideleNorm_archPart_eq_prod (x : (AdeleRing (𝓞 K) K)ˣ) :
    ideleNorm K (archPart x) =
      ∏ w : InfinitePlace K, ideleNorm K (archUnitHom w (infiniteUnitsComponent (𝓞 K) K w x)) := by
  rw [archPart_eq_prod]
  simp only [ideleNorm, map_prod, NNReal.coe_prod]

theorem prod_ofReal_cpow {α : Type} (t : Finset α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (s : ℂ) :
    ∏ a ∈ t, ((f a : ℝ) : ℂ) ^ s = (((∏ a ∈ t, f a) : ℝ) : ℂ) ^ s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun b _ => hf b)]

theorem continuous_of_continuous_coe (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (h : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) : Continuous χ := by
  refine Units.continuous_iff.mpr ⟨h, ?_⟩
  have : (fun z : (AdeleRing (𝓞 K) K)ˣ => (((χ z)⁻¹ : ℂˣ) : ℂ)) =
      (fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) ∘ fun z => z⁻¹ := by
    funext z; simp only [Function.comp_apply, map_inv]
  rw [this]
  exact h.comp continuous_inv

theorem ideleNorm_principal (k : Kˣ) :
    ideleNorm K (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k) = 1 := by
  simp only [ideleNorm]
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := ⟨rfl⟩
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap K k
  rw [show (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k) =
      Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom k from rfl, h]
  rfl

theorem apply_eq_one_of_mem_sup
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ))
    (hic : IsIdeleClassChar (𝓞 K) K χ)
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt χ v)
    (σ₀ : ℝ)
    (harch : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      ((archLocalChar χ v x : ℂˣ) : ℂ) =
        (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((σ₀ : ℝ) : ℂ) * Complex.I))
    (a : (AdeleRing (𝓞 K) K)ˣ) (ha : a ∈ normOneIdeles K)
    (hmem : a ∈ principalIdeles (𝓞 K) K ⊔
      NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (∅ : Set (HeightOneSpectrum (𝓞 K)))) :
    χ a = 1 := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hmem
  obtain ⟨k, rfl⟩ := hy

  have hk : χ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k) = 1 := hic k

  have hz1 : ideleNorm K z = 1 := by
    have h := (mem_normOneIdeles_iff _).mp ha
    rw [ideleNorm_mul, ideleNorm_principal, one_mul] at h
    exact h

  have hzU : finitePartUnits (𝓞 K) K z ∈ FiniteAdeleRing.unitIdeles (𝓞 K) K := by
    rw [← FiniteAdeleRing.unitIdelesOutside_empty]
    exact (NumberField.AdeleRing.mem_unitIdelesOutside_iff _ z).mp hz
  have hzfU : finitePartUnits (𝓞 K) K (finPart z) ∈ FiniteAdeleRing.unitIdeles (𝓞 K) K := by
    rw [finitePartUnits_finPart]; exact hzU

  have hχc : Continuous χ := continuous_of_continuous_coe χ hc
  have hfin : χ (finPart z) = 1 :=
    NumberField.TateGlobal.apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous K χ hχc ∅
      (fun v _ => hram v) (finPart z) rfl (fun v hv => absurd hv (Finset.notMem_empty v)) hzfU

  have hfin1 : ideleNorm K (finPart z) = 1 :=
    NumberField.TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles K (finPart z) rfl hzfU
  have harch1 : ideleNorm K (archPart z) = 1 := by
    have h := congrArg (ideleNorm K) (archPart_mul_finPart z)
    rw [ideleNorm_mul, hfin1, mul_one, hz1] at h
    exact h

  have harchval : ((χ (archPart z) : ℂˣ) : ℂ) = 1 := by
    rw [map_archPart_eq_prod, Units.coe_prod]
    simp only [harch]
    rw [prod_ofReal_cpow _ _ (fun w => (ideleNorm_pos _).le), ← ideleNorm_archPart_eq_prod, harch1]
    simp
  have harch' : χ (archPart z) = 1 := Units.ext harchval
  rw [map_mul, hk, one_mul, ← archPart_mul_finPart z, map_mul, harch', hfin, one_mul]

end C3cAux

open C3cAux

theorem solution (K : Type) [Field K] [NumberField K] :
    ∃ N : ℕ, ∀ (ι : Type) (χ : ι → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ)) (σ₀ : ι → ℝ),
      (∀ i, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ i z : ℂˣ) : ℂ)) →
      (∀ i, IsIdeleClassChar (𝓞 K) K (χ i)) →
      (∀ i (v : HeightOneSpectrum (𝓞 K)), NumberField.TateGlobal.IsUnramifiedCharAt (χ i) v) →
      (∀ i (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ((NumberField.TateGlobal.archLocalChar (χ i) v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((σ₀ i : ℝ) : ℂ) * Complex.I)) →
      (∀ i j, i ≠ j → ∃ z ∈ NumberField.TateGlobal.normOneIdeles K, χ i z ≠ χ j z) →
      Finite ι ∧ Nat.card ι ≤ N := by
  classical

  set PU : Subgroup (AdeleRing (𝓞 K) K)ˣ := principalIdeles (𝓞 K) K ⊔
      NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (∅ : Set (HeightOneSpectrum (𝓞 K))) with hPU
  haveI hfi : PU.FiniteIndex := by
    have h := NumberField.AdeleRing.finiteIndex_principalIdeles_sup_unitIdelesOutside K K (∅ : Finset _)
    simp only [Finset.notMem_empty, Set.setOf_false] at h
    exact h
  set A : Subgroup (AdeleRing (𝓞 K) K)ˣ := normOneIdeles K with hA
  set H : Subgroup ↥A := PU.subgroupOf A with hH
  haveI : H.FiniteIndex := inferInstance
  haveI : H.Normal := inferInstance
  haveI hQfin : Finite (↥A ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  set n : ℕ := Nat.card (↥A ⧸ H) with hn
  haveI : NeZero n := ⟨(Nat.card_pos (α := ↥A ⧸ H)).ne'⟩
  refine ⟨Nat.card (↥A ⧸ H → ↥(rootsOfUnity n ℂ)), ?_⟩
  intro ι χ σ₀ hc hic hram harch hne

  let ψ : ι → (↥A →* ℂˣ) := fun i => (χ i).comp A.subtype
  have hker : ∀ i, H ≤ (ψ i).ker := by
    intro i a ha
    rw [MonoidHom.mem_ker]
    show χ i (a : (AdeleRing (𝓞 K) K)ˣ) = 1
    exact apply_eq_one_of_mem_sup (χ i) (hc i) (hic i) (hram i) (σ₀ i) (harch i) a a.2
      (Subgroup.mem_subgroupOf.mp ha)
  let ψq : ι → (↥A ⧸ H →* ℂˣ) := fun i => QuotientGroup.lift H (ψ i) (hker i)
  have hψq : ∀ i (a : ↥A), ψq i (QuotientGroup.mk a) = χ i (a : (AdeleRing (𝓞 K) K)ˣ) := fun i a => rfl

  have hroot : ∀ i (q : ↥A ⧸ H), ψq i q ∈ rootsOfUnity n ℂ := by
    intro i q
    rw [mem_rootsOfUnity, ← map_pow, pow_card_eq_one', map_one]
  let F : ι → (↥A ⧸ H → ↥(rootsOfUnity n ℂ)) := fun i q => ⟨ψq i q, hroot i q⟩
  have hinj : Function.Injective F := by
    intro i j hij
    by_contra hne'
    obtain ⟨z, hz, hz'⟩ := hne i j hne'
    apply hz'
    have h1 := congrFun hij (QuotientGroup.mk ⟨z, hz⟩)
    have h2 : ψq i (QuotientGroup.mk ⟨z, hz⟩) = ψq j (QuotientGroup.mk ⟨z, hz⟩) := congrArg Subtype.val h1
    rwa [hψq, hψq] at h2
  exact ⟨Finite.of_injective F hinj, Nat.card_le_card_of_injective F hinj⟩

end
end S_NumberField_TateGlobal_exists_forall_finite_and_card_le_of_archLocalChar_eq_cpow_const_of_pairwise_ne_normOneIdeles
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_forall_finite_and_card_le_of_archLocalChar_eq_cpow_const_of_pairwise_ne_normOneIdeles (solution)
