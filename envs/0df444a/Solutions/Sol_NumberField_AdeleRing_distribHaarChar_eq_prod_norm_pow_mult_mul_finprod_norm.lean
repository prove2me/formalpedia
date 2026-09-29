-- Prove2me | solution 1 for NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/baf024f6-3ae1-5f23-98ea-ac382c062105

import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm

set_option Elab.async false

section RHMODFold_JE2aFlatAdelic

set_option autoImplicit false

noncomputable section

p2m_open "NumberField P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField NumberField.AdelicHeight NumberField.AdelicLevel IsDedekindDomain"
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates

namespace P6B
namespace JE2aFlat

variable (F : Type) [Field F] [NumberField F]

def placeModulus (x : (AdeleRing (𝓞 F) F)ˣ) : ℝ :=
  (∏ w : InfinitePlace F, ‖(x : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult)
    * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(x : AdeleRing (𝓞 F) F).2 v‖

variable {F}

theorem finComp_mul_finComp_inv (x : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (x : AdeleRing (𝓞 F) F).2 v * ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1 := by
  have h : ((x : AdeleRing (𝓞 F) F) * ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).2 v = 1 := by
    rw [x.mul_inv]; rfl
  exact h

theorem finComp_ne_zero (x : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (x : AdeleRing (𝓞 F) F).2 v ≠ 0 := by
  intro h0
  have h := finComp_mul_finComp_inv x v
  rw [h0, zero_mul] at h
  exact zero_ne_one h

theorem norm_finComp_eventually_eq_one (x : (AdeleRing (𝓞 F) F)ˣ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ‖(x : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
  have hx := ((x : AdeleRing (𝓞 F) F).2).2
  have hx' := (((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2).2
  filter_upwards [hx, hx'] with v hv hv'
  have h1 : ‖(x : AdeleRing (𝓞 F) F).2 v‖ ≤ 1 := norm_le_one_of_mem_adicCompletionIntegers hv
  have h2 : ‖((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v‖ ≤ 1 :=
    norm_le_one_of_mem_adicCompletionIntegers hv'
  have hprod : ‖(x : AdeleRing (𝓞 F) F).2 v‖
      * ‖((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
    rw [← norm_mul, finComp_mul_finComp_inv, norm_one]
  refine le_antisymm h1 ?_
  by_contra hlt
  push Not at hlt
  have := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt h2
  rw [hprod] at this
  exact lt_irrefl _ this

theorem hasFiniteMulSupport_norm_finComp (x : (AdeleRing (𝓞 F) F)ˣ) :
    (fun v : HeightOneSpectrum (𝓞 F) => ‖(x : AdeleRing (𝓞 F) F).2 v‖).HasFiniteMulSupport :=
  Filter.eventually_cofinite.mp (norm_finComp_eventually_eq_one x)

end P6B.JE2aFlat

end

end RHMODFold_JE2aFlatAdelic

section RHMODFold_JE2aHMod1

p2m_open "NumberField P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField NumberField.AdelicBox IsDedekindDomain IsDedekindDomain.HeightOneSpectrum"
open scoped RestrictedProduct

noncomputable section

namespace P6B
namespace JE2aHMod

variable (F : Type) [Field F] [NumberField F]

def zhatAddSubgroup : AddSubgroup (FiniteAdeleRing (𝓞 F) F) where
  carrier := integralFiniteAdeles (𝓞 F) F
  zero_mem' := fun _ => zero_mem _
  add_mem' := fun hx hy v => add_mem (hx v) (hy v)
  neg_mem' := fun hx v => neg_mem (hx v)

@[scoped simp] theorem mem_zhatAddSubgroup {x : FiniteAdeleRing (𝓞 F) F} :
    x ∈ zhatAddSubgroup F ↔ x ∈ integralFiniteAdeles (𝓞 F) F := Iff.rfl

theorem mul_apply (a b : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    (a * b) v = a v * b v := rfl

theorem one_apply (v : HeightOneSpectrum (𝓞 F)) :
    (1 : FiniteAdeleRing (𝓞 F) F) v = 1 := rfl

theorem zero_apply (v : HeightOneSpectrum (𝓞 F)) :
    (0 : FiniteAdeleRing (𝓞 F) F) v = 0 := rfl

theorem neg_apply (a : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    (-a) v = -a v := rfl

theorem isUnit_apply (y : (FiniteAdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    IsUnit ((y : FiniteAdeleRing (𝓞 F) F) v) := by
  refine ⟨⟨(y : FiniteAdeleRing (𝓞 F) F) v, ((y⁻¹ : _) : FiniteAdeleRing (𝓞 F) F) v, ?_, ?_⟩, rfl⟩
  · rw [← mul_apply, y.mul_inv, one_apply]
  · rw [← mul_apply, y.inv_mul, one_apply]

theorem inv_apply (y : (FiniteAdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ((y⁻¹ : _) : FiniteAdeleRing (𝓞 F) F) v = ((y : FiniteAdeleRing (𝓞 F) F) v)⁻¹ :=
  eq_inv_of_mul_eq_one_right
    (show (y : FiniteAdeleRing (𝓞 F) F) v * ((y⁻¹ : _) : FiniteAdeleRing (𝓞 F) F) v = 1 by
      rw [← mul_apply, y.mul_inv, one_apply])

theorem valued_apply_ne_zero (y : (FiniteAdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr (isUnit_apply F y v).ne_zero

def ySmulZhat (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (_hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    AddSubgroup (FiniteAdeleRing (𝓞 F) F) where
  carrier := {z | ∀ v : HeightOneSpectrum (𝓞 F),
    Valued.v (z v) ≤ Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v)}
  zero_mem' := fun v => by rw [zero_apply, map_zero]; exact zero_le'
  add_mem' := fun {a b} ha hb v => (Valuation.map_add _ _ _).trans (max_le (ha v) (hb v))
  neg_mem' := fun {a} ha v => by rw [neg_apply, Valuation.map_neg]; exact ha v

@[scoped simp] theorem mem_ySmulZhat_iff (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F)
    {z : FiniteAdeleRing (𝓞 F) F} :
    z ∈ ySmulZhat F y hy ↔ ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (z v) ≤ Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) := Iff.rfl

theorem ySmulZhat_le_zhat (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    ySmulZhat F y hy ≤ zhatAddSubgroup F := fun _ hz v =>
  (mem_adicCompletionIntegers _ _ _).mpr
    ((hz v).trans ((mem_adicCompletionIntegers _ _ _).mp (hy v)))

theorem smul_integralFiniteAdeles_eq_ySmulZhat (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    ((fun a => (y : FiniteAdeleRing (𝓞 F) F) * a) '' integralFiniteAdeles (𝓞 F) F)
      = (ySmulZhat F y hy : Set (FiniteAdeleRing (𝓞 F) F)) := by
  ext z; constructor
  · rintro ⟨a, ha, rfl⟩ v
    rw [mul_apply, Valuation.map_mul]
    exact mul_le_of_le_one_right' ((mem_adicCompletionIntegers _ _ _).mp (ha v))
  · intro hz
    refine ⟨((y⁻¹ : _) : FiniteAdeleRing (𝓞 F) F) * z, fun v => ?_, ?_⟩
    · rw [mem_adicCompletionIntegers, mul_apply, Valuation.map_mul, inv_apply, map_inv₀,
        inv_mul_le_one₀ (zero_lt_iff.mpr (valued_apply_ne_zero F y v))]
      exact hz v
    · show (y : FiniteAdeleRing (𝓞 F) F) * (_ * z) = z
      rw [← mul_assoc, y.mul_inv, one_mul]

theorem finite_support_not_unit (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    {v : HeightOneSpectrum (𝓞 F) |
      ¬ IsUnit (⟨(y : FiniteAdeleRing (𝓞 F) F) v, hy v⟩ : v.adicCompletionIntegers F)}.Finite := by

  have hfin : {v : HeightOneSpectrum (𝓞 F) |
      ((y⁻¹ : _) : FiniteAdeleRing (𝓞 F) F) v ∉ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.mp
      (show Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]
        from ((y⁻¹ : _) : FiniteAdeleRing (𝓞 F) F)).eventually
  refine hfin.subset fun v hv hinv => hv ?_

  refine ⟨⟨⟨(y : FiniteAdeleRing (𝓞 F) F) v, hy v⟩,
    ⟨((y⁻¹ : _) : FiniteAdeleRing (𝓞 F) F) v, hinv⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (show (y : FiniteAdeleRing (𝓞 F) F) v
      * ((y⁻¹ : _) : FiniteAdeleRing (𝓞 F) F) v = 1 by
      rw [← mul_apply, y.mul_inv, one_apply])
  · exact Subtype.ext (show ((y⁻¹ : _) : FiniteAdeleRing (𝓞 F) F) v
      * (y : FiniteAdeleRing (𝓞 F) F) v = 1 by
      rw [← mul_apply, y.inv_mul, one_apply])

def globalIdeal (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    Ideal (𝓞 F) where
  carrier := {r | algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r ∈ ySmulZhat F y hy}
  zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]; exact (ySmulZhat F y hy).zero_mem
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_add]; exact (ySmulZhat F y hy).add_mem ha hb
  smul_mem' := fun c {r} hr v => by
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at hr ⊢
    rw [mul_apply, Valuation.map_mul]
    exact (mul_le_of_le_one_left zero_le'
      ((mem_adicCompletionIntegers _ _ _).mp
        (algebraMap_mem_adicCompletionIntegers _ F v c))).trans (hr v)

theorem mem_globalIdeal_iff (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) {r : 𝓞 F} :
    r ∈ globalIdeal F y hy ↔ ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r v)
        ≤ Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) := Iff.rfl

theorem globalIdeal_ne_bot (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    globalIdeal F y hy ≠ ⊥ := by
  obtain ⟨s, hs0, hsy⟩ := exists_mul_mem_integralFiniteAdeles (𝓞 F) F
    ((y⁻¹ : _) : FiniteAdeleRing (𝓞 F) F)
  rw [Submodule.ne_bot_iff]
  refine ⟨s, fun v => ?_, hs0⟩

  have := (mem_adicCompletionIntegers _ _ _).mp (hsy v)
  rw [mul_apply, Valuation.map_mul, inv_apply, map_inv₀] at this
  calc Valued.v (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) s v)
      = Valued.v (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) s v)
        * (Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v))⁻¹
        * Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) := by
          rw [mul_assoc, inv_mul_cancel₀ (valued_apply_ne_zero F y v), mul_one]
    _ ≤ 1 * Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) := by gcongr; exact this
    _ = Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) := one_mul _

theorem surjective_zhat_mod_ySmulZhat (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F)
    (z : zhatAddSubgroup F) :
    ∃ a : 𝓞 F, ((⟨algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) a,
        fun v => algebraMap_mem_adicCompletionIntegers _ F v a⟩ : zhatAddSubgroup F) - z)
      ∈ (ySmulZhat F y hy).addSubgroupOf (zhatAddSubgroup F) := by

  obtain ⟨s, hs_mem, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (globalIdeal_ne_bot F y hy)
  obtain ⟨a, ha⟩ := exists_forall_valued_sub_le (𝓞 F) F (z := (z : FiniteAdeleRing (𝓞 F) F))
    z.2 (s := s) hs0
  refine ⟨a, fun v => ?_⟩
  show Valued.v (((⟨algebraMap _ _ a, _⟩ - z : zhatAddSubgroup F) : FiniteAdeleRing (𝓞 F) F) v)
    ≤ Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v)
  calc Valued.v (((⟨algebraMap _ _ a, _⟩ - z : zhatAddSubgroup F) : FiniteAdeleRing (𝓞 F) F) v)
      = Valued.v ((z : FiniteAdeleRing (𝓞 F) F) v
        - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) := by
          rw [Valuation.map_sub_swap]; rfl
    _ ≤ Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s)) := ha v
    _ = Valued.v ((algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) s) v) := by rfl
    _ ≤ Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) := hs_mem v

theorem finite_zhat_quot_ySmulZhat (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    Finite (zhatAddSubgroup F ⧸ (ySmulZhat F y hy).addSubgroupOf (zhatAddSubgroup F)) := by

  have hfin : Finite ((𝓞 F) ⧸ globalIdeal F y hy) :=
    (globalIdeal F y hy).finiteQuotientOfFreeOfNeBot (globalIdeal_ne_bot F y hy)

  set H := (ySmulZhat F y hy).addSubgroupOf (zhatAddSubgroup F)
  let q : (𝓞 F) →+ zhatAddSubgroup F ⧸ H :=
    (QuotientAddGroup.mk' H).comp
      { toFun := fun a => ⟨algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) a,
          fun v => algebraMap_mem_adicCompletionIntegers _ F v a⟩
        map_zero' := Subtype.ext (map_zero _)
        map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }
  have hsurj : Function.Surjective q := by
    refine Quotient.ind fun z => ?_
    obtain ⟨a, ha⟩ := surjective_zhat_mod_ySmulZhat F y hy z
    exact ⟨a, (QuotientAddGroup.eq_iff_sub_mem).mpr ha⟩

  have hker : ∀ a b : 𝓞 F, Submodule.quotientRel (globalIdeal F y hy) a b → q a = q b := by
    intro a b hab
    have hmem : -a + b ∈ globalIdeal F y hy := QuotientAddGroup.leftRel_apply.mp hab
    rw [eq_comm, show q b = q a ↔ q b - q a = 0 from sub_eq_zero.symm, ← map_sub]
    exact (QuotientAddGroup.eq_zero_iff _).mpr
      (by rw [show b - a = -a + b from by ring]; exact hmem)

  let f : (𝓞 F) ⧸ globalIdeal F y hy → zhatAddSubgroup F ⧸ H :=
    fun c => Quotient.liftOn' c q hker
  have hfsurj : Function.Surjective f := fun z => by
    obtain ⟨a, ha⟩ := hsurj z
    exact ⟨Ideal.Quotient.mk _ a, ha⟩
  exact Finite.of_surjective f hfsurj

def quotZhatHom (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    (𝓞 F) →+ zhatAddSubgroup F ⧸ (ySmulZhat F y hy).addSubgroupOf (zhatAddSubgroup F) :=
  (QuotientAddGroup.mk' _).comp
    { toFun := fun a => ⟨algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) a,
        fun v => algebraMap_mem_adicCompletionIntegers _ F v a⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }

theorem ker_quotZhatHom (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    (quotZhatHom F y hy).ker = (globalIdeal F y hy).toAddSubgroup := by
  ext a; simp only [AddMonoidHom.mem_ker, quotZhatHom, AddMonoidHom.coe_comp,
    QuotientAddGroup.coe_mk', Function.comp_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  rfl

theorem surjective_quotZhatHom (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    Function.Surjective (quotZhatHom F y hy) := by
  refine Quotient.ind fun z => ?_
  obtain ⟨a, ha⟩ := surjective_zhat_mod_ySmulZhat F y hy z
  exact ⟨a, (QuotientAddGroup.eq_iff_sub_mem).mpr ha⟩

theorem card_zhat_quot_eq_absNorm (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    Nat.card (zhatAddSubgroup F ⧸ (ySmulZhat F y hy).addSubgroupOf (zhatAddSubgroup F))
      = Ideal.absNorm (globalIdeal F y hy) := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot, ← ker_quotZhatHom F y hy]
  exact (Nat.card_congr
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (surjective_quotZhatHom F y hy)).toEquiv).symm

def ordNat (y : (FiniteAdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  (-((WithZero.unzero (valued_apply_ne_zero F y v)).toAdd)).toNat

theorem valued_eq_exp_neg_ordNat (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F)
    (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) = WithZero.exp (-(ordNat F y v : ℤ)) := by
  have hle : (WithZero.unzero (valued_apply_ne_zero F y v)).toAdd ≤ 0 := by
    have := (mem_adicCompletionIntegers _ _ _).mp (hy v)
    rwa [← WithZero.coe_unzero (valued_apply_ne_zero F y v), ← WithZero.coe_one,
      WithZero.coe_le_coe, ← ofAdd_toAdd (WithZero.unzero _),
      show (1 : Multiplicative ℤ) = Multiplicative.ofAdd (0 : ℤ) from rfl,
      Multiplicative.ofAdd_le] at this
  rw [ordNat, Int.toNat_of_nonneg (neg_nonneg.mpr hle), neg_neg, WithZero.exp,
    ofAdd_toAdd, WithZero.coe_unzero]

theorem toAdd_unzero_eq_neg_ordNat (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F)
    (v : HeightOneSpectrum (𝓞 F)) :
    (WithZero.unzero (valued_apply_ne_zero F y v)).toAdd = -(ordNat F y v : ℤ) := by
  have := valued_eq_exp_neg_ordNat F y hy v
  rw [← WithZero.coe_unzero (valued_apply_ne_zero F y v), WithZero.exp,
    WithZero.coe_inj] at this
  rw [← toAdd_ofAdd (-(ordNat F y v : ℤ)), ← this]

theorem mem_globalIdeal_iff_forall_mem_pow (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) (r : 𝓞 F) :
    r ∈ globalIdeal F y hy ↔ ∀ v : HeightOneSpectrum (𝓞 F), r ∈ v.asIdeal ^ ordNat F y v := by
  rw [mem_globalIdeal_iff]
  refine forall_congr' fun v => ?_
  have hval : Valued.v ((algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r) v) = v.intValuation r := by
    have h1 : Valued.v ((algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r) v)
        = Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r)) := rfl
    rw [h1, AdelicBox.valued_algebraMap (𝓞 F) F v r]
  rw [hval, valued_eq_exp_neg_ordNat F y hy v, HeightOneSpectrum.intValuation_le_pow_iff_mem]

theorem ordNat_eq_zero_of_isUnit (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F)
    (v : HeightOneSpectrum (𝓞 F))
    (hu : IsUnit (⟨(y : FiniteAdeleRing (𝓞 F) F) v, hy v⟩ : v.adicCompletionIntegers F)) :
    ordNat F y v = 0 := by

  have h1 : Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) = 1 := by
    obtain ⟨u, hu⟩ := hu
    have huv : (((u : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F)
        : v.adicCompletion F) = (y : FiniteAdeleRing (𝓞 F) F) v := congrArg Subtype.val hu
    have huvinv : (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F)
        : v.adicCompletion F) * (y : FiniteAdeleRing (𝓞 F) F) v = 1 := by
      rw [← huv]; exact_mod_cast u.inv_mul
    refine le_antisymm ((mem_adicCompletionIntegers _ _ _).mp (hy v)) ?_
    have hinvle : Valued.v (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F)
        : v.adicCompletion F) ≤ 1 :=
      (mem_adicCompletionIntegers _ _ _).mp
        ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F).2
    have hone : Valued.v (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F)
          : v.adicCompletion F)
        * Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) = 1 := by
      rw [← Valuation.map_mul, huvinv, map_one]
    calc (1 : WithZero (Multiplicative ℤ)) = _ := hone.symm
      _ ≤ 1 * Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) := by gcongr
      _ = _ := one_mul _

  simp only [ordNat]
  rw [show WithZero.unzero (valued_apply_ne_zero F y v) = (1 : Multiplicative ℤ) from by
    rw [← WithZero.coe_inj, WithZero.coe_unzero, h1]; rfl, toAdd_one, neg_zero, Int.toNat_zero]

theorem norm_apply_eq_one_of_isUnit (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F)
    (v : HeightOneSpectrum (𝓞 F))
    (hu : IsUnit (⟨(y : FiniteAdeleRing (𝓞 F) F) v, hy v⟩ : v.adicCompletionIntegers F)) :
    ‖(y : FiniteAdeleRing (𝓞 F) F) v‖ = 1 := by
  rw [NumberField.FinitePlace.norm_def, valued_eq_exp_neg_ordNat F y hy v,
    ordNat_eq_zero_of_isUnit F y hy v hu, Nat.cast_zero, neg_zero,
    show WithZero.exp (0 : ℤ) = (1 : WithZero (Multiplicative ℤ)) from rfl,
    map_one, NNReal.coe_one]

theorem absNorm_globalIdeal_mul_finprod_norm (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    (Ideal.absNorm (globalIdeal F y hy) : ℝ)
      * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(y : FiniteAdeleRing (𝓞 F) F) v‖ = 1 := by
  classical
  set S := (finite_support_not_unit F y hy).toFinset with hS

  have hI : globalIdeal F y hy = ∏ v ∈ S, v.asIdeal ^ ordNat F y v := by
    have hinf : globalIdeal F y hy = S.inf (fun v => v.asIdeal ^ ordNat F y v) := by
      ext r
      rw [mem_globalIdeal_iff_forall_mem_pow, Finset.inf_eq_iInf]
      simp only [Ideal.mem_iInf]
      constructor
      · exact fun h v _ => h v
      · intro h v
        by_cases hv : v ∈ S
        · exact h v hv
        · rw [ordNat_eq_zero_of_isUnit F y hy v
            (by simpa [hS, Set.Finite.mem_toFinset] using hv), pow_zero, Ideal.one_eq_top]
          exact trivial
    rw [hinf]
    exact HeightOneSpectrum.inf_pow_eq_prod S (ordNat F y) (fun v => v)
      (fun i _ j _ hij => hij)

  have hN : (Ideal.absNorm (globalIdeal F y hy) : ℝ)
      = ∏ v ∈ S, ((Ideal.absNorm v.asIdeal : ℝ)) ^ ordNat F y v := by
    rw [hI, map_prod]
    push_cast
    exact Finset.prod_congr rfl fun v _ => by rw [map_pow]; push_cast; ring

  have hNorm : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(y : FiniteAdeleRing (𝓞 F) F) v‖
      = ∏ v ∈ S, ((Ideal.absNorm v.asIdeal : ℝ)) ^ (-(ordNat F y v : ℤ)) := by
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) ?_]
    · refine Finset.prod_congr rfl fun v _ => ?_
      rw [NumberField.FinitePlace.norm_def,
        WithZeroMulInt.toNNReal_neg_apply _ (valued_apply_ne_zero F y v),
        toAdd_unzero_eq_neg_ordNat F y hy v]
      push_cast
      ring
    · intro v hv
      rw [Function.mem_mulSupport] at hv
      rw [Finset.mem_coe, hS, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      intro hu; exact hv (norm_apply_eq_one_of_isUnit F y hy v hu)

  rw [hN, hNorm, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun v _ => ?_
  have hq : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
    ((Ideal.absNorm_ne_zero_iff _).mpr (v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot))
  rw [← zpow_natCast, ← zpow_add₀ hq, add_neg_cancel, zpow_zero]

theorem card_zhat_quot_mul_finprod_norm (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    (Nat.card (zhatAddSubgroup F ⧸ (ySmulZhat F y hy).addSubgroupOf (zhatAddSubgroup F)) : ℝ)
      * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(y : FiniteAdeleRing (𝓞 F) F) v‖ = 1 := by
  rw [card_zhat_quot_eq_absNorm F y hy]
  exact absNorm_globalIdeal_mul_finprod_norm F y hy

section AuditHMod1
end AuditHMod1

end P6B.JE2aHMod
p2m_reactivate "P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B.JE2aHMod"
p2m_reactivate "P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B"
end
p2m_reactivate "P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B.JE2aHMod"

end RHMODFold_JE2aHMod1
p2m_reactivate "P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B.JE2aHMod"

section RHMODFold_JE2aHMod2

set_option Elab.async false

set_option autoImplicit false

p2m_open "MeasureTheory Complex NumberField P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField NumberField.InfinitePlace IsDedekindDomain"
open IsDedekindDomain.HeightOneSpectrum TopologicalSpace Filter
open scoped Pointwise ENNReal NNReal

noncomputable section

namespace NumberField
p2m_export "NumberField" "FinitePlace InfiniteAdeleRing mk place RingOfIntegers InfinitePlace AdeleRing FinitePlace.norm_def AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one AdelicBox.integralFiniteAdeles AdelicBox.algebraMap_mem_adicCompletionIntegers AdelicBox.valued_algebraMap AdelicBox.exists_mul_mem_integralFiniteAdeles AdelicBox.properSpace_completion AdelicBox.isCompact_integralFiniteAdeles AdelicBox.isOpen_integralFiniteAdeles"
namespace AdelicCountability
p2m_open "NumberField"

scoped instance instCountableIdeal (R : Type*) [CommRing R] [Countable R] [IsNoetherianRing R] :
    Countable (Ideal R) := by
  have hsurj : Function.Surjective (fun s : Finset R => Ideal.span (s : Set R)) := by
    intro I
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I)
    exact ⟨s, hs⟩
  exact hsurj.countable

scoped instance instCountableHeightOneSpectrum (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Countable R] : Countable (HeightOneSpectrum R) := by
  have hinj : Function.Injective (fun v : HeightOneSpectrum R => v.asIdeal) := by
    intro v w h
    exact HeightOneSpectrum.ext h
  exact hinj.countable

scoped instance instCountableValueGroup₀ {R Γ₀ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]
    [Countable Γ₀] (v : R →*₀ Γ₀) : Countable (MonoidWithZeroHom.ValueGroup₀ v) :=
  MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective.countable

scoped instance instCountableUnits {M : Type*} [Monoid M] [Countable M] : Countable Mˣ :=
  Units.val_injective.countable

scoped instance instCountableWithZero {α : Type*} [Countable α] : Countable (WithZero α) := by
  classical
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat α
  refine ⟨⟨fun x => if h : x = 0 then 0 else f (WithZero.unzero h) + 1, fun a b hab => ?_⟩⟩
  dsimp only [] at hab
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · rw [ha, hb]
  · rw [dif_pos ha, dif_neg hb] at hab
    exact absurd hab.symm (Nat.succ_ne_zero _)
  · rw [dif_neg ha, dif_pos hb] at hab
    exact absurd hab (Nat.succ_ne_zero _)
  · rw [dif_neg ha, dif_neg hb] at hab
    rw [← WithZero.coe_unzero ha, ← WithZero.coe_unzero hb, hf (Nat.add_right_cancel hab)]

theorem isCountablyGenerated_uniformity_of_valued (R : Type*) (Γ₀ : Type*) [Ring R]
    [LinearOrderedCommGroupWithZero Γ₀] [Countable Γ₀] [vR : Valued R Γ₀] :
    (uniformity R).IsCountablyGenerated :=
  (Valued.hasBasis_uniformity R Γ₀).isCountablyGenerated

scoped instance instSecondCountableAdicCompletion (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Countable K] (v : HeightOneSpectrum R) :
    SecondCountableTopology (v.adicCompletion K) := by
  have hcg : (uniformity (v.adicCompletion K)).IsCountablyGenerated :=
    isCountablyGenerated_uniformity_of_valued _ (WithZero (Multiplicative ℤ))
  have hsep : SeparableSpace (v.adicCompletion K) := by
    have : Countable (WithVal (v.valuation K)) :=
      (WithVal.equiv (v.valuation K)).toEquiv.injective.countable
    exact (IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion_surjective K v).denseRange.separableSpace
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion K v)
  exact UniformSpace.secondCountable_of_separable _

open RestrictedProduct Topology in
theorem secondCountableTopology_restrictedProduct {ι : Type*} [Countable ι]
    {R : ι → Type*} {B : ∀ i, Set (R i)}
    [∀ i, TopologicalSpace (R i)] [∀ i, SecondCountableTopology (R i)]
    (hBo : ∀ i, IsOpen (B i)) :
    SecondCountableTopology (Πʳ i, [R i, B i]_[Filter.cofinite]) := by

  have hprin : ∀ t : Finset ι, Filter.cofinite ≤ Filter.principal ((↑t : Set ι)ᶜ) := fun t =>
    Filter.le_principal_iff.mpr (Filter.mem_cofinite.mpr (by simp))

  have hpiece : ∀ t : Finset ι,
      SecondCountableTopology (Πʳ i, [R i, B i]_[Filter.principal ((↑t : Set ι)ᶜ)]) := fun t =>
    (isEmbedding_coe_of_principal).secondCountableTopology

  set U : Finset ι → Set (Πʳ i, [R i, B i]_[Filter.cofinite]) :=
    fun t => Set.range (inclusion R B (hprin t)) with hU
  have hUopen : ∀ t, IsOpen (U t) := fun t =>
    (isOpenEmbedding_inclusion_principal hBo (hprin t)).isOpen_range
  have hUsc : ∀ t, SecondCountableTopology (U t) := by
    intro t
    haveI := hpiece t
    exact (((isOpenEmbedding_inclusion_principal hBo (hprin t)).isEmbedding.toHomeomorph).symm).isEmbedding.secondCountableTopology
  have hcover : ⋃ t : Finset ι, U t = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have hfin : {i | x.1 i ∉ B i}.Finite := Filter.eventually_cofinite.mp x.2
    refine ⟨hfin.toFinset, ⟨x.1, ?_⟩, rfl⟩
    rw [Filter.eventually_principal]
    intro i hi
    by_contra hmem
    exact hi (by simpa using hfin.mem_toFinset.mpr hmem)
  exact TopologicalSpace.secondCountableTopology_of_countable_cover hUopen hcover

open IsDedekindDomain in
open scoped RestrictedProduct in

scoped instance instSecondCountableFiniteAdeleRing (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Countable R] [Countable K] :
    SecondCountableTopology (FiniteAdeleRing R K) := by
  haveI : SecondCountableTopology
      (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]) :=
    secondCountableTopology_restrictedProduct fun v => Valued.isOpen_valuationSubring _
  exact inferInstanceAs <| SecondCountableTopology <|
    Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]

scoped instance instSecondCountableInfiniteAdeleRing (K : Type*) [Field K] [NumberField K] :
    SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI : ∀ v : InfinitePlace K, SecondCountableTopology v.Completion := by
    intro v
    haveI : Countable (WithAbs v.1) := (WithAbs.equiv v.1).toEquiv.injective.countable
    haveI : TopologicalSpace.SeparableSpace v.Completion :=
      (NumberField.InfinitePlace.Completion.ofCompletion_surjective v).denseRange.separableSpace
        (NumberField.InfinitePlace.Completion.continuous_ofCompletion v)
    exact UniformSpace.secondCountable_of_separable _
  exact inferInstanceAs <| SecondCountableTopology <| (v : InfinitePlace K) → v.Completion

scoped instance instSecondCountableAdeleRing (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [NumberField K] [Algebra R K] [IsFractionRing R K] [Countable R] :
    SecondCountableTopology (AdeleRing R K) :=
  inferInstanceAs <| SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing R K)

scoped instance instCountableRingOfIntegers (K : Type*) [Field K] [NumberField K] :
    Countable (NumberField.RingOfIntegers K) :=
  Subtype.countable

end NumberField.AdelicCountability
p2m_reactivate "P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B.JE2aHMod P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField.AdelicCountability"
p2m_reactivate "P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B.JE2aHMod P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField"

namespace M4aS4

theorem map_mul_left_volume_real {c : ℝ} (hc : c ≠ 0) :
    (volume : Measure ℝ).map (fun x => c * x) = ‖c‖ₑ⁻¹ • volume := by
  have h := Real.map_volume_mul_left hc
  rw [show ((c * ·) : ℝ → ℝ) = fun x => c * x from rfl] at h
  rw [h, abs_inv, ENNReal.ofReal_inv_of_pos (abs_pos.mpr hc), Real.enorm_eq_ofReal_abs]

theorem det_restrictScalars_mulLeft_complex (c : ℂ) :
    LinearMap.det ((LinearMap.mulLeft ℂ c).restrictScalars ℝ) = normSq c := by
  rw [← LinearMap.det_toMatrix basisOneI]
  have hM : (LinearMap.toMatrix basisOneI basisOneI ((LinearMap.mulLeft ℂ c).restrictScalars ℝ))
      = !![c.re, -c.im; c.im, c.re] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hM, Matrix.det_fin_two_of]
  simp [normSq_apply]

theorem map_mul_left_volume_complex {c : ℂ} (hc : c ≠ 0) :
    (volume : Measure ℂ).map (fun x => c * x) = (‖c‖ₑ ^ 2)⁻¹ • volume := by
  have hdet : LinearMap.det ((LinearMap.mulLeft ℂ c).restrictScalars ℝ) ≠ 0 := by
    rw [det_restrictScalars_mulLeft_complex]
    exact (normSq_pos.mpr hc).ne'
  have hfun : (fun x => c * x) = ⇑((LinearMap.mulLeft ℂ c).restrictScalars ℝ) := by
    ext x; simp [LinearMap.mulLeft_apply]
  have habs : |LinearMap.det ((LinearMap.mulLeft ℂ c).restrictScalars ℝ)| = ‖c‖ ^ 2 := by
    rw [det_restrictScalars_mulLeft_complex, abs_of_nonneg (normSq_nonneg c), normSq_eq_norm_sq]
  calc (volume : Measure ℂ).map (fun x => c * x)
      = volume.map ⇑((LinearMap.mulLeft ℂ c).restrictScalars ℝ) := by rw [← hfun]
    _ = ENNReal.ofReal |(LinearMap.det ((LinearMap.mulLeft ℂ c).restrictScalars ℝ))⁻¹| • volume :=
        Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet
    _ = (‖c‖ₑ ^ 2)⁻¹ • volume := by
        rw [abs_inv, habs, ENNReal.ofReal_inv_of_pos (pow_pos (norm_pos_iff.mpr hc) 2),
          ENNReal.ofReal_pow (norm_nonneg c), ofReal_norm]

theorem volume_image_mul_left_real {c : ℝ} (hc : c ≠ 0) {S : Set ℝ} (hS : MeasurableSet S) :
    volume ((fun x => c * x) '' S) = ‖c‖ₑ * volume S := by
  have himg : (fun x => c * x) '' S = (fun x => c⁻¹ * x) ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [inv_mul_cancel_left₀ hc] using hx
    · intro hy
      exact ⟨c⁻¹ * y, hy, by field_simp⟩
  rw [himg, ← Measure.map_apply (measurable_const_mul _) hS,
    map_mul_left_volume_real (inv_ne_zero hc)]
  simp [Measure.smul_apply, smul_eq_mul, enorm_inv, hc]

theorem volume_image_mul_left_complex {c : ℂ} (hc : c ≠ 0) {S : Set ℂ} (hS : MeasurableSet S) :
    volume ((fun x => c * x) '' S) = ‖c‖ₑ ^ 2 * volume S := by
  have himg : (fun x => c * x) '' S = (fun x => c⁻¹ * x) ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [inv_mul_cancel_left₀ hc] using hx
    · intro hy
      exact ⟨c⁻¹ * y, hy, by field_simp⟩
  rw [himg, ← Measure.map_apply (measurable_const_mul _) hS,
    map_mul_left_volume_complex (inv_ne_zero hc)]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [enorm_inv hc, ENNReal.inv_pow, inv_inv]

variable (F : Type) [Field F] [NumberField F]

@[reducible] def placeBorel (w : InfinitePlace F) : MeasurableSpace (w.Completion) := borel _

attribute [local instance] placeBorel

scoped instance placeBorelSpace (w : InfinitePlace F) : BorelSpace (w.Completion) := ⟨rfl⟩

variable {F}

def placeMeasureReal {w : InfinitePlace F} (hw : w.IsReal) : Measure (w.Completion) :=
  (volume : Measure ℝ).map (Completion.ringEquivRealOfIsReal hw).symm

def placeMeasureComplex {w : InfinitePlace F} (hw : w.IsComplex) : Measure (w.Completion) :=
  (volume : Measure ℂ).map (Completion.ringEquivComplexOfIsComplex hw).symm

variable (F) in
open Classical in

def placeMeasure (w : InfinitePlace F) : Measure (w.Completion) :=
  if hw : w.IsReal then placeMeasureReal hw
  else placeMeasureComplex (not_isReal_iff_isComplex.mp hw)

scoped instance isAddHaarMeasure_placeMeasureReal {w : InfinitePlace F} (hw : w.IsReal) :
    (placeMeasureReal hw).IsAddHaarMeasure := by
  unfold placeMeasureReal
  exact AddEquiv.isAddHaarMeasure_map _
    ((Completion.ringEquivRealOfIsReal hw).symm : ℝ ≃+* w.Completion).toAddEquiv
    (Completion.isometryEquivRealOfIsReal hw).symm.continuous
    (Completion.isometryEquivRealOfIsReal hw).continuous

scoped instance isAddHaarMeasure_placeMeasureComplex {w : InfinitePlace F} (hw : w.IsComplex) :
    (placeMeasureComplex hw).IsAddHaarMeasure := by
  unfold placeMeasureComplex
  exact AddEquiv.isAddHaarMeasure_map _
    ((Completion.ringEquivComplexOfIsComplex hw).symm : ℂ ≃+* w.Completion).toAddEquiv
    (Completion.isometryEquivComplexOfIsComplex hw).symm.continuous
    (Completion.isometryEquivComplexOfIsComplex hw).continuous

scoped instance secondCountable_completion (w : InfinitePlace F) :
    SecondCountableTopology (w.Completion) := by
  rcases w.isReal_or_isComplex with hw | hw
  · exact (Completion.isometryEquivRealOfIsReal hw).toHomeomorph.isEmbedding.secondCountableTopology
  · exact (Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.isEmbedding.secondCountableTopology

omit [NumberField F] in

theorem placeMeasureReal_image_mul {w : InfinitePlace F} (hw : w.IsReal)
    {a : w.Completion} (ha : a ≠ 0) {S : Set (w.Completion)} (hS : MeasurableSet S) :
    placeMeasureReal hw ((fun x => a * x) '' S) = ‖a‖ₑ * placeMeasureReal hw S := by
  set e := Completion.ringEquivRealOfIsReal hw with he
  have hea : e a ≠ 0 := fun h => ha (by simpa using congrArg e.symm h)
  have hmeas_symm : Measurable (⇑e.symm) :=
    (Completion.isometryEquivRealOfIsReal hw).symm.continuous.measurable
  have himgS : MeasurableSet ((fun x => a * x) '' S) := by
    have heq : (fun x => a * x) '' S = (Homeomorph.mulLeft₀ a ha).toMeasurableEquiv '' S := rfl
    rw [heq, MeasurableEquiv.measurableSet_image]
    exact hS
  have hpre : ⇑e.symm ⁻¹' ((fun x => a * x) '' S) = (fun r => e a * r) '' (⇑e.symm ⁻¹' S) := by
    ext r
    constructor
    · rintro ⟨s, hs, hsr⟩
      refine ⟨e s, by simpa using hs, ?_⟩
      have := congrArg e hsr
      simpa [map_mul] using this
    · rintro ⟨t, ht, rfl⟩
      exact ⟨e.symm t, ht, by simp [map_mul]⟩
  have hnorm : ‖e a‖ = ‖a‖ := by
    have h0 : e (0 : w.Completion) = 0 := map_zero e
    calc ‖e a‖ = dist (e a) (e 0) := by rw [h0, dist_zero_right]
      _ = dist a 0 := (Completion.isometry_extensionEmbeddingOfIsReal hw).dist_eq a 0
      _ = ‖a‖ := dist_zero_right a
  have henorm : ‖e a‖ₑ = ‖a‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, hnorm]
  unfold placeMeasureReal
  rw [Measure.map_apply hmeas_symm himgS, Measure.map_apply hmeas_symm hS, hpre,
    volume_image_mul_left_real hea (hmeas_symm hS), henorm]

omit [NumberField F] in

theorem placeMeasureComplex_image_mul {w : InfinitePlace F} (hw : w.IsComplex)
    {a : w.Completion} (ha : a ≠ 0) {S : Set (w.Completion)} (hS : MeasurableSet S) :
    placeMeasureComplex hw ((fun x => a * x) '' S) = ‖a‖ₑ ^ 2 * placeMeasureComplex hw S := by
  set e := Completion.ringEquivComplexOfIsComplex hw with he
  have hea : e a ≠ 0 := fun h => ha (by simpa using congrArg e.symm h)
  have hmeas_symm : Measurable (⇑e.symm) :=
    (Completion.isometryEquivComplexOfIsComplex hw).symm.continuous.measurable
  have himgS : MeasurableSet ((fun x => a * x) '' S) := by
    have heq : (fun x => a * x) '' S = (Homeomorph.mulLeft₀ a ha).toMeasurableEquiv '' S := rfl
    rw [heq, MeasurableEquiv.measurableSet_image]
    exact hS
  have hpre : ⇑e.symm ⁻¹' ((fun x => a * x) '' S) = (fun r => e a * r) '' (⇑e.symm ⁻¹' S) := by
    ext r
    constructor
    · rintro ⟨s, hs, hsr⟩
      refine ⟨e s, by simpa using hs, ?_⟩
      have := congrArg e hsr
      simpa [map_mul] using this
    · rintro ⟨t, ht, rfl⟩
      exact ⟨e.symm t, ht, by simp [map_mul]⟩
  have hnorm : ‖e a‖ = ‖a‖ := by
    have h0 : e (0 : w.Completion) = 0 := map_zero e
    calc ‖e a‖ = dist (e a) (e 0) := by rw [h0, dist_zero_right]
      _ = dist a 0 := (Completion.isometry_extensionEmbedding w).dist_eq a 0
      _ = ‖a‖ := dist_zero_right a
  have henorm : ‖e a‖ₑ = ‖a‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, hnorm]
  unfold placeMeasureComplex
  rw [Measure.map_apply hmeas_symm himgS, Measure.map_apply hmeas_symm hS, hpre,
    volume_image_mul_left_complex hea (hmeas_symm hS), henorm]

omit [NumberField F] in

theorem placeMeasure_image_mul (w : InfinitePlace F) {a : w.Completion} (ha : a ≠ 0)
    {S : Set (w.Completion)} (hS : MeasurableSet S) :
    placeMeasure F w ((fun x => a * x) '' S) = ‖a‖ₑ ^ w.mult * placeMeasure F w S := by
  unfold placeMeasure
  split
  · next hw =>
    rw [placeMeasureReal_image_mul hw ha hS,
      show w.mult = 1 from by simp [mult, hw], pow_one]
  · next hw =>
    rw [placeMeasureComplex_image_mul (not_isReal_iff_isComplex.mp hw) ha hS,
      show w.mult = 2 from by simp [mult, hw]]

scoped instance isAddHaarMeasure_placeMeasure (w : InfinitePlace F) :
    (placeMeasure F w).IsAddHaarMeasure := by
  unfold placeMeasure
  split
  · exact isAddHaarMeasure_placeMeasureReal _
  · exact isAddHaarMeasure_placeMeasureComplex _

scoped instance sigmaCompact_completion (w : InfinitePlace F) : SigmaCompactSpace (w.Completion) :=
  inferInstance

scoped instance sigmaFinite_placeMeasure (w : InfinitePlace F) : SigmaFinite (placeMeasure F w) :=
  inferInstance

variable (F) in

def archMeasure : Measure ((w : InfinitePlace F) → w.Completion) :=
  Measure.pi (fun w => placeMeasure F w)

scoped instance isFiniteMeasureOnCompacts_archMeasure : IsFiniteMeasureOnCompacts (archMeasure F) := by
  unfold archMeasure; infer_instance

scoped instance isOpenPosMeasure_archMeasure : (archMeasure F).IsOpenPosMeasure := by
  unfold archMeasure; infer_instance

scoped instance sigmaFinite_archMeasure : SigmaFinite (archMeasure F) := by
  unfold archMeasure; infer_instance

scoped instance isAddLeftInvariant_archMeasure : (archMeasure F).IsAddLeftInvariant := by
  constructor
  intro a
  have hmeas : Measurable (fun x : (w : InfinitePlace F) → w.Completion => a + x) :=
    measurable_const.add measurable_id
  refine Eq.symm (Measure.pi_eq fun B hB => ?_)
  have hpre : (fun x : (w : InfinitePlace F) → w.Completion => a + x) ⁻¹' Set.pi Set.univ B
      = Set.pi Set.univ (fun w => (fun t => a w + t) ⁻¹' B w) := by
    ext x
    simp [Set.mem_pi, Pi.add_apply]
  unfold archMeasure
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hB), hpre, Measure.pi_pi]
  refine Finset.prod_congr rfl fun w _ => ?_
  exact measure_preimage_add (placeMeasure F w) (a w) (B w)

scoped instance isAddHaarMeasure_archMeasure : (archMeasure F).IsAddHaarMeasure :=
  { toIsFiniteMeasureOnCompacts := inferInstance
    toIsAddLeftInvariant := inferInstance
    toIsOpenPosMeasure := inferInstance }

omit [NumberField F] in

theorem image_mul_pi (a : (w : InfinitePlace F) → w.Completion)
    (B : (w : InfinitePlace F) → Set (w.Completion)) :
    (fun x => a * x) '' Set.pi Set.univ B
      = Set.pi Set.univ (fun w => (fun t => a w * t) '' B w) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    intro w _
    exact ⟨y w, hy w (Set.mem_univ w), rfl⟩
  · intro hx
    choose b hb hab using fun w => hx w (Set.mem_univ w)
    refine ⟨fun w => b w, fun w _ => hb w, ?_⟩
    funext w
    exact hab w

theorem archMeasure_image_mul_pi (a : (w : InfinitePlace F) → w.Completion)
    (ha : ∀ w, a w ≠ 0) (B : (w : InfinitePlace F) → Set (w.Completion))
    (hB : ∀ w, MeasurableSet (B w)) :
    archMeasure F ((fun x => a * x) '' Set.pi Set.univ B)
      = (∏ w, ‖a w‖ₑ ^ w.mult) * archMeasure F (Set.pi Set.univ B) := by
  rw [image_mul_pi a B]
  unfold archMeasure
  rw [Measure.pi_pi, Measure.pi_pi]
  calc ∏ w, placeMeasure F w ((fun t => a w * t) '' B w)
      = ∏ w, (‖a w‖ₑ ^ w.mult * placeMeasure F w (B w)) := by
        refine Finset.prod_congr rfl fun w _ => ?_
        exact placeMeasure_image_mul w (ha w) (hB w)
    _ = (∏ w, ‖a w‖ₑ ^ w.mult) * ∏ w, placeMeasure F w (B w) := Finset.prod_mul_distrib

scoped instance properSpace_completion₀ (w : InfinitePlace F) : ProperSpace (w.Completion) :=
  AdelicBox.properSpace_completion F w

omit [NumberField F] in
theorem placeMeasure_pos_closedBall (w : InfinitePlace F) :
    0 < placeMeasure F w (Metric.closedBall (0 : w.Completion) 1) :=
  ((Metric.isOpen_ball (x := (0 : w.Completion)) (ε := 1)).measure_pos (placeMeasure F w)
    (Metric.nonempty_ball.mpr one_pos)).trans_le
    (measure_mono Metric.ball_subset_closedBall)

omit [NumberField F] in
theorem placeMeasure_closedBall_lt_top (w : InfinitePlace F) :
    placeMeasure F w (Metric.closedBall (0 : w.Completion) 1) < ⊤ :=
  (isCompact_closedBall (0 : w.Completion) 1).measure_lt_top

variable (F) in
@[reducible] def infMS : MeasurableSpace (InfiniteAdeleRing F) :=
  inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))

attribute [local instance] infMS

scoped instance infBorelSpace : BorelSpace (InfiniteAdeleRing F) :=
  inferInstanceAs (BorelSpace ((w : InfinitePlace F) → w.Completion))

variable (F) in
@[reducible] def finBorel : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _

attribute [local instance] finBorel

scoped instance finBorelSpace : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩

variable (F) in
@[reducible] def adeleMS : MeasurableSpace (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (MeasurableSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

attribute [local instance] adeleMS

scoped instance adeleBorelSpaceProd : BorelSpace (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (BorelSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

scoped instance secondCountable_infiniteAdeles : SecondCountableTopology (InfiniteAdeleRing F) :=
  inferInstanceAs (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))

scoped instance secondCountable_adeleRing : SecondCountableTopology (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

variable (F) in

def zhatCompacts : TopologicalSpace.PositiveCompacts (FiniteAdeleRing (𝓞 F) F) where
  carrier := AdelicBox.integralFiniteAdeles (𝓞 F) F
  isCompact' := AdelicBox.isCompact_integralFiniteAdeles F
  interior_nonempty' := by
    rw [(AdelicBox.isOpen_integralFiniteAdeles F).interior_eq]
    exact ⟨0, fun v => zero_mem _⟩

variable (F) in

def finMeasure : Measure (FiniteAdeleRing (𝓞 F) F) :=
  Measure.addHaarMeasure (zhatCompacts F)

scoped instance isAddHaarMeasure_finMeasure : (finMeasure F).IsAddHaarMeasure := by
  unfold finMeasure; infer_instance

scoped instance sigmaFinite_finMeasure : SigmaFinite (finMeasure F) := by
  unfold finMeasure; infer_instance

variable (F) in

def infMeasure : Measure (InfiniteAdeleRing F) := archMeasure F

scoped instance isAddHaarMeasure_infMeasure : (infMeasure F).IsAddHaarMeasure :=
  inferInstanceAs ((archMeasure F).IsAddHaarMeasure)

scoped instance sigmaFinite_infMeasure : SigmaFinite (infMeasure F) :=
  inferInstanceAs (SigmaFinite (archMeasure F))

variable (F) in
def adelicMeasure : Measure (AdeleRing (𝓞 F) F) :=
  (infMeasure F).prod (finMeasure F)

scoped instance isAddHaarMeasure_adelicMeasure : (adelicMeasure F).IsAddHaarMeasure :=
  inferInstanceAs
    ((((infMeasure F).prod (finMeasure F)) :
      Measure (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)).IsAddHaarMeasure)

scoped instance sigmaFinite_adelicMeasure : SigmaFinite (adelicMeasure F) :=
  inferInstanceAs (SigmaFinite
    (((infMeasure F).prod (finMeasure F)) :
      Measure (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)))

variable (F) in

def refSet : Set (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) :=
  (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) ×ˢ
    (AdelicBox.integralFiniteAdeles (𝓞 F) F)

variable (F) in
theorem isCompact_refSet : IsCompact (refSet F) :=
  (isCompact_univ_pi fun w => isCompact_closedBall (0 : w.Completion) 1).prod
    (AdelicBox.isCompact_integralFiniteAdeles F)

variable (F) in
theorem interior_refSet_nonempty : (interior (refSet F)).Nonempty := by
  have hopen : IsOpen ((Set.univ.pi fun w : InfinitePlace F => Metric.ball (0 : w.Completion) 1)
      ×ˢ (AdelicBox.integralFiniteAdeles (𝓞 F) F)) :=
    (isOpen_set_pi Set.finite_univ fun w _ => Metric.isOpen_ball).prod
      (AdelicBox.isOpen_integralFiniteAdeles F)
  have hsub : ((Set.univ.pi fun w : InfinitePlace F => Metric.ball (0 : w.Completion) 1)
      ×ˢ (AdelicBox.integralFiniteAdeles (𝓞 F) F)) ⊆ refSet F :=
    Set.prod_mono (Set.pi_mono fun w _ => Metric.ball_subset_closedBall) le_rfl
  have hmem : ((0 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F)) ∈
      ((Set.univ.pi fun w : InfinitePlace F => Metric.ball (0 : w.Completion) 1)
        ×ˢ (AdelicBox.integralFiniteAdeles (𝓞 F) F)) := by
    refine Set.mem_prod.mpr ⟨fun w _ => ?_, fun v => zero_mem _⟩
    exact Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1)
  exact ⟨_, interior_maximal hsub hopen hmem⟩

variable (F) in
theorem adelicMeasure_refSet_ne_top :
    (archMeasure F).prod (finMeasure F) (refSet F) ≠ ⊤ := by
  unfold refSet
  rw [Measure.prod_prod]
  exact ENNReal.mul_ne_top
    (by
      show archMeasure F _ ≠ ⊤
      unfold archMeasure
      rw [Measure.pi_pi]
      exact (ENNReal.prod_lt_top fun w _ => placeMeasure_closedBall_lt_top w).ne)
    ((AdelicBox.isCompact_integralFiniteAdeles F).measure_lt_top).ne

set_option synthInstance.maxHeartbeats 640000 in
scoped instance regular_adelicMeasure : (adelicMeasure F).Regular :=
  Measure.regular_of_isAddLeftInvariant (μ := adelicMeasure F)
    (K := refSet F) (isCompact_refSet F) (interior_refSet_nonempty F)
    (adelicMeasure_refSet_ne_top F)

variable (F) in
theorem finMeasure_zhat : finMeasure F (AdelicBox.integralFiniteAdeles (𝓞 F) F) = 1 :=
  Measure.addHaarMeasure_self (K₀ := zhatCompacts F)

variable (F) in
theorem adelicMeasure_refSet_ne_zero :
    (archMeasure F).prod (finMeasure F) (refSet F) ≠ 0 := by
  unfold refSet
  rw [Measure.prod_prod]
  refine mul_ne_zero ?_ ?_
  · show archMeasure F _ ≠ 0
    unfold archMeasure
    rw [Measure.pi_pi]
    exact Finset.prod_ne_zero_iff.mpr fun w _ => (placeMeasure_pos_closedBall w).ne'
  · rw [finMeasure_zhat]
    exact one_ne_zero

end M4aS4
p2m_reactivate "P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B.JE2aHMod P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField.AdelicCountability P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.M4aS4"

namespace M4aS4

attribute [local instance] placeBorel infMS finBorel adeleMS

variable {F : Type} [Field F] [NumberField F]

def HasTransversal (y : FiniteAdeleRing (𝓞 F) F) : Prop :=
  ∃ T : Finset (FiniteAdeleRing (𝓞 F) F),
    (↑T ⊆ AdelicBox.integralFiniteAdeles (𝓞 F) F) ∧
    ((T.card : ℝ) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖y v‖ = 1) ∧
    (↑T : Set (FiniteAdeleRing (𝓞 F) F)).PairwiseDisjoint
        (fun t => t +ᵥ (y • AdelicBox.integralFiniteAdeles (𝓞 F) F)) ∧
    (⋃ t ∈ T, t +ᵥ (y • AdelicBox.integralFiniteAdeles (𝓞 F) F))
        = AdelicBox.integralFiniteAdeles (𝓞 F) F

theorem measurableSet_smul_zhat (y : FiniteAdeleRing (𝓞 F) F) :
    MeasurableSet (y • AdelicBox.integralFiniteAdeles (𝓞 F) F) := by
  rw [← Set.image_smul]
  exact ((AdelicBox.isCompact_integralFiniteAdeles F).image (continuous_const_smul y)).isClosed.measurableSet

theorem finMeasure_smul_zhat {y : FiniteAdeleRing (𝓞 F) F} (hT : HasTransversal y) :
    finMeasure F (y • AdelicBox.integralFiniteAdeles (𝓞 F) F)
      = ENNReal.ofReal (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖y v‖) := by
  obtain ⟨T, -, hcard, hdisj, hcover⟩ := hT
  have hmeas : MeasurableSet (y • AdelicBox.integralFiniteAdeles (𝓞 F) F) := measurableSet_smul_zhat y
  have hsum : finMeasure F (AdelicBox.integralFiniteAdeles (𝓞 F) F)
      = ∑ t ∈ T, finMeasure F (t +ᵥ (y • AdelicBox.integralFiniteAdeles (𝓞 F) F)) := by
    conv_lhs => rw [← hcover]
    exact measure_biUnion_finset hdisj fun t _ => hmeas.const_vadd t
  simp only [measure_vadd, Finset.sum_const, nsmul_eq_mul, finMeasure_zhat] at hsum

  have hcard0 : (0 : ℝ) < T.card := by
    rcases (Nat.cast_nonneg (α := ℝ) T.card).eq_or_lt with h | h
    · rw [← h, zero_mul] at hcard; exact absurd hcard zero_ne_one
    · exact h
  have hm : finMeasure F (y • AdelicBox.integralFiniteAdeles (𝓞 F) F) = ((T.card : ℝ≥0∞))⁻¹ := by
    rw [ENNReal.eq_inv_of_mul_eq_one_left hsum.symm, inv_inv]
  have hr : (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖y v‖) = (T.card : ℝ)⁻¹ :=
    eq_inv_of_mul_eq_one_right hcard
  rw [hm, hr, ENNReal.ofReal_inv_of_pos hcard0, ENNReal.ofReal_natCast]

theorem distribHaarChar_of_fst_eq_one (a : (AdeleRing (𝓞 F) F)ˣ) (ha : (a : AdeleRing (𝓞 F) F).1 = 1)
    (hT : HasTransversal (a : AdeleRing (𝓞 F) F).2) :
    (distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(a : AdeleRing (𝓞 F) F).2 v‖ := by
  classical
  set y : FiniteAdeleRing (𝓞 F) F := (a : AdeleRing (𝓞 F) F).2 with hy
  have hr0 : 0 ≤ ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖y v‖ := finprod_nonneg fun v => norm_nonneg _
  set r : ℝ≥0 := ⟨∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖y v‖, hr0⟩ with hrdef
  have hr : ENNReal.ofReal (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖y v‖) = (r : ℝ≥0∞) :=
    ENNReal.ofReal_eq_coe_nnreal hr0
  have hs₀ : adelicMeasure F (show Set (AdeleRing (𝓞 F) F) from refSet F) ≠ 0 :=
    adelicMeasure_refSet_ne_zero F
  have hsfin : adelicMeasure F (show Set (AdeleRing (𝓞 F) F) from refSet F) ≠ ⊤ :=
    adelicMeasure_refSet_ne_top F

  have hsplit : (a • (show Set (AdeleRing (𝓞 F) F) from refSet F))
      = (show Set (AdeleRing (𝓞 F) F) from
          ((Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) ×ˢ
            (y • AdelicBox.integralFiniteAdeles (𝓞 F) F))) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, ⟨z.2, hz.2, rfl⟩⟩
      show ((a : AdeleRing (𝓞 F) F) * z).1 ∈ _
      rw [show ((a : AdeleRing (𝓞 F) F) * z).1 = (a : AdeleRing (𝓞 F) F).1 * z.1 from rfl, ha, one_mul]
      exact hz.1
    · rintro ⟨hx1, ⟨z2, hz2, hxz2⟩⟩
      refine ⟨(show AdeleRing (𝓞 F) F from ((show InfiniteAdeleRing F from x.1), z2)), ⟨hx1, hz2⟩,
        Prod.ext ?_ ?_⟩
      · show (a : AdeleRing (𝓞 F) F).1 * x.1 = x.1
        rw [ha, one_mul]
      · show (a : AdeleRing (𝓞 F) F).2 * z2 = x.2
        exact hxz2
  have hcompute : (archMeasure F).prod (finMeasure F)
      (((Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) ×ˢ
        (y • AdelicBox.integralFiniteAdeles (𝓞 F) F)))
      = ENNReal.ofReal (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖y v‖)
        * (archMeasure F).prod (finMeasure F) (refSet F) := by
    unfold refSet
    rw [Measure.prod_prod, Measure.prod_prod, finMeasure_smul_zhat hT, finMeasure_zhat, mul_one, mul_comm]
  have hμgs : adelicMeasure F (a • (show Set (AdeleRing (𝓞 F) F) from refSet F))
      = (r : ℝ≥0∞) * adelicMeasure F (show Set (AdeleRing (𝓞 F) F) from refSet F) := by
    rw [hsplit, ← hr]
    exact hcompute
  have key := distribHaarChar_eq_of_measure_smul_eq_mul (μ := adelicMeasure F)
    (s := (show Set (AdeleRing (𝓞 F) F) from refSet F)) (g := a) hs₀ hsfin hμgs
  rw [key]
  rfl

end M4aS4
p2m_reactivate "P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B.JE2aHMod P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField.AdelicCountability P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.M4aS4"

end
p2m_reactivate "P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B.JE2aHMod P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField.AdelicCountability P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.M4aS4"

end RHMODFold_JE2aHMod2
p2m_reactivate "P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B.JE2aHMod P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField.AdelicCountability P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.M4aS4"

section RHMODFold_JE2aHMod1b

p2m_open "NumberField P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField NumberField.AdelicBox IsDedekindDomain IsDedekindDomain.HeightOneSpectrum"
open scoped RestrictedProduct Pointwise

noncomputable section

namespace P6B
namespace JE2aHMod

variable (F : Type) [Field F] [NumberField F]

theorem coe_ySmulZhat_eq_smul (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    (ySmulZhat F y hy : Set (FiniteAdeleRing (𝓞 F) F))
      = (y : FiniteAdeleRing (𝓞 F) F) • integralFiniteAdeles (𝓞 F) F := by
  rw [← smul_integralFiniteAdeles_eq_ySmulZhat F y hy, ← Set.image_smul]
  rfl

theorem hasTransversal (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    M4aS4.HasTransversal (y : FiniteAdeleRing (𝓞 F) F) := by
  classical
  set H := (ySmulZhat F y hy).addSubgroupOf (zhatAddSubgroup F) with hH
  haveI := finite_zhat_quot_ySmulZhat F y hy
  haveI : Fintype (zhatAddSubgroup F ⧸ H) := Fintype.ofFinite _

  set T : Finset (FiniteAdeleRing (𝓞 F) F) :=
    Finset.univ.image (fun c : zhatAddSubgroup F ⧸ H =>
      ((Quotient.out c : zhatAddSubgroup F) : FiniteAdeleRing (𝓞 F) F))
    with hT
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  ·
    intro t ht
    simp only [hT, Finset.coe_image, Set.mem_image, Finset.coe_univ, Set.mem_univ,
      true_and] at ht
    obtain ⟨c, rfl⟩ := ht
    exact (Quotient.out c).2
  ·
    have hcard : T.card = Nat.card (zhatAddSubgroup F ⧸ H) := by
      rw [hT, Finset.card_image_of_injective _ ?_, Finset.card_univ, Nat.card_eq_fintype_card]
      intro c₁ c₂ heq
      have : (Quotient.out c₁ : zhatAddSubgroup F) = Quotient.out c₂ :=
        Subtype.val_injective heq
      rw [← Quotient.out_eq c₁, ← Quotient.out_eq c₂, this]
    rw [hcard]
    exact card_zhat_quot_mul_finprod_norm F y hy
  ·
    rw [← coe_ySmulZhat_eq_smul F y hy]
    intro t₁ ht₁ t₂ ht₂ hne
    simp only [hT, Finset.coe_image, Set.mem_image, Finset.coe_univ, Set.mem_univ,
      true_and] at ht₁ ht₂
    obtain ⟨c₁, rfl⟩ := ht₁; obtain ⟨c₂, rfl⟩ := ht₂
    rw [Function.onFun, Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
    rintro w ⟨⟨a₁, ha₁, hw₁⟩, ⟨a₂, ha₂, hw₂⟩⟩

    apply hne

    have h₁ : ((Quotient.out c₁ : zhatAddSubgroup F) : FiniteAdeleRing (𝓞 F) F) + a₁ = w := hw₁
    have h₂ : ((Quotient.out c₂ : zhatAddSubgroup F) : FiniteAdeleRing (𝓞 F) F) + a₂ = w := hw₂
    have hdiff : ((Quotient.out c₁ - Quotient.out c₂ : zhatAddSubgroup F)
        : FiniteAdeleRing (𝓞 F) F) ∈ ySmulZhat F y hy := by
      have hsub : ((Quotient.out c₁ - Quotient.out c₂ : zhatAddSubgroup F)
          : FiniteAdeleRing (𝓞 F) F) = a₂ - a₁ := by
        push_cast
        linear_combination h₁ - h₂
      rw [hsub]; exact (ySmulZhat F y hy).sub_mem ha₂ ha₁
    have : c₁ = c₂ := by
      rw [← Quotient.out_eq c₁, ← Quotient.out_eq c₂, QuotientAddGroup.eq_iff_sub_mem]
      exact hdiff
    rw [this]
  ·
    rw [← coe_ySmulZhat_eq_smul F y hy]
    apply Set.Subset.antisymm
    · rintro w ⟨_, ⟨t, rfl⟩, _, ⟨ht, rfl⟩, ⟨a, ha, rfl⟩⟩
      simp only [hT, Finset.mem_image, Finset.mem_univ, true_and] at ht
      obtain ⟨c, rfl⟩ := ht
      simp only [vadd_eq_add]
      exact add_mem (Quotient.out c).2 (ySmulZhat_le_zhat F y hy ha)
    · intro z hz
      set zc : zhatAddSubgroup F := ⟨z, hz⟩
      refine Set.mem_iUnion₂.mpr ⟨((Quotient.out (⟦zc⟧ : zhatAddSubgroup F ⧸ H)
        : zhatAddSubgroup F) : FiniteAdeleRing (𝓞 F) F), ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨⟦zc⟧, Finset.mem_univ _, rfl⟩
      · refine ⟨z - ((Quotient.out (⟦zc⟧ : _ ⧸ H) : zhatAddSubgroup F) : _), ?_, by
          simp [vadd_eq_add]⟩

        have : zc - Quotient.out (⟦zc⟧ : _ ⧸ H) ∈ H :=
          QuotientAddGroup.eq_iff_sub_mem.mp (Quotient.out_eq _).symm
        exact this

section AuditHMod1b
end AuditHMod1b
p2m_reactivate "P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B.JE2aHMod P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField.AdelicCountability P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.M4aS4"

end P6B.JE2aHMod
p2m_reactivate "P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B.JE2aHMod P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField.AdelicCountability P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.M4aS4"
p2m_reactivate "P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B.JE2aHMod P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField.AdelicCountability P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.M4aS4"
end
p2m_reactivate "P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B.JE2aHMod P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField.AdelicCountability P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.M4aS4"

end RHMODFold_JE2aHMod1b
p2m_reactivate "P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B.JE2aHMod P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField.AdelicCountability P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.M4aS4"

section RHMODFold_JE2aHMod3

set_option autoImplicit false

noncomputable section

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField NumberField.AdelicLevel IsDedekindDomain"
open M4aS4 P6B.JE2aFlat AutomorphicForm
open scoped NNReal

namespace P6B
namespace JE2aHMod

variable {F : Type} [Field F] [NumberField F]

def finUnit (u : (FiniteAdeleRing (𝓞 F) F)ˣ) : (AdeleRing (𝓞 F) F)ˣ where
  val := (show AdeleRing (𝓞 F) F from ((1 : InfiniteAdeleRing F), (u : FiniteAdeleRing (𝓞 F) F)))
  inv := (show AdeleRing (𝓞 F) F from
    ((1 : InfiniteAdeleRing F), ((u⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)))
  val_inv := Prod.ext (one_mul 1) u.mul_inv
  inv_val := Prod.ext (one_mul 1) u.inv_mul

theorem finUnit_fst (u : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    ((finUnit u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := rfl

theorem finUnit_snd (u : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    ((finUnit u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = u := rfl

theorem finUnit_mul (u v : (FiniteAdeleRing (𝓞 F) F)ˣ) : finUnit (u * v) = finUnit u * finUnit v :=
  Units.ext (Prod.ext (one_mul (1 : InfiniteAdeleRing F)).symm rfl)

def finPartUnit (x : (AdeleRing (𝓞 F) F)ˣ) : (FiniteAdeleRing (𝓞 F) F)ˣ where
  val := (x : AdeleRing (𝓞 F) F).2
  inv := ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2
  val_inv := by
    have h := congrArg Prod.snd x.mul_inv
    exact h
  inv_val := by
    have h := congrArg Prod.snd x.inv_mul
    exact h

def archUnit (x : (AdeleRing (𝓞 F) F)ˣ) : (AdeleRing (𝓞 F) F)ˣ := x * (finUnit (finPartUnit x))⁻¹

theorem eq_archUnit_mul_finUnit (x : (AdeleRing (𝓞 F) F)ˣ) : x = archUnit x * finUnit (finPartUnit x) :=
  (inv_mul_cancel_right x _).symm

theorem archUnit_fst (x : (AdeleRing (𝓞 F) F)ˣ) :
    ((archUnit x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = (x : AdeleRing (𝓞 F) F).1 := by
  show (x : AdeleRing (𝓞 F) F).1 * (1 : InfiniteAdeleRing F) = (x : AdeleRing (𝓞 F) F).1
  exact mul_one _

theorem archUnit_snd (x : (AdeleRing (𝓞 F) F)ˣ) :
    ((archUnit x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := by
  show (x : AdeleRing (𝓞 F) F).2 * ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1
  have h := congrArg Prod.snd x.mul_inv
  exact h

theorem hasFiniteMulSupport_norm (u : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    (fun v : HeightOneSpectrum (𝓞 F) => ‖(u : FiniteAdeleRing (𝓞 F) F) v‖).HasFiniteMulSupport :=
  hasFiniteMulSupport_norm_finComp (finUnit u)

theorem finprod_norm_pos (u : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    0 < ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(u : FiniteAdeleRing (𝓞 F) F) v‖ :=
  finprod_induction (fun r : ℝ => 0 < r) one_pos (fun _ _ => mul_pos)
    fun v => norm_pos_iff.mpr (finComp_ne_zero (finUnit u) v)

theorem finprod_norm_mul (u w : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖((u * w : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v‖)
      = (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(u : FiniteAdeleRing (𝓞 F) F) v‖)
        * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(w : FiniteAdeleRing (𝓞 F) F) v‖ := by
  rw [← finprod_mul_distrib (hasFiniteMulSupport_norm u) (hasFiniteMulSupport_norm w)]
  refine finprod_congr fun v => ?_
  rw [Units.val_mul, show ((u : FiniteAdeleRing (𝓞 F) F) * (w : FiniteAdeleRing (𝓞 F) F)) v
      = (u : FiniteAdeleRing (𝓞 F) F) v * (w : FiniteAdeleRing (𝓞 F) F) v from rfl, norm_mul]

theorem distribHaarChar_finUnit_of_hasTransversal (w : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hw : HasTransversal (w : FiniteAdeleRing (𝓞 F) F)) :
    (distribHaarChar (AdeleRing (𝓞 F) F) (finUnit w) : ℝ)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(w : FiniteAdeleRing (𝓞 F) F) v‖ :=
  distribHaarChar_of_fst_eq_one (finUnit w) rfl hw

theorem distribHaarChar_finUnit
    (hT : ∀ y : (FiniteAdeleRing (𝓞 F) F)ˣ,
      (y : FiniteAdeleRing (𝓞 F) F) ∈ AdelicBox.integralFiniteAdeles (𝓞 F) F →
        HasTransversal (y : FiniteAdeleRing (𝓞 F) F))
    (u : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    (distribHaarChar (AdeleRing (𝓞 F) F) (finUnit u) : ℝ)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(u : FiniteAdeleRing (𝓞 F) F) v‖ := by

  obtain ⟨s, hs0, hsu⟩ :=
    AdelicBox.exists_mul_mem_integralFiniteAdeles (𝓞 F) F (u : FiniteAdeleRing (𝓞 F) F)
  have hsK : algebraMap (𝓞 F) F s ≠ 0 := fun h =>
    hs0 ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective (𝓞 F) F) s h)
  have hsA : IsUnit (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) s) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F)]
    exact (isUnit_iff_ne_zero.mpr hsK).map _
  obtain ⟨sU, hsUval⟩ : ∃ sU : (FiniteAdeleRing (𝓞 F) F)ˣ,
      (sU : FiniteAdeleRing (𝓞 F) F) = algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) s :=
    ⟨hsA.unit, hsA.unit_spec⟩

  have hsZ : (sU : FiniteAdeleRing (𝓞 F) F) ∈ AdelicBox.integralFiniteAdeles (𝓞 F) F := by
    intro v
    rw [hsUval]
    change algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s) ∈ _
    exact AdelicBox.algebraMap_mem_adicCompletionIntegers (𝓞 F) F v s
  have hsuZ : ((sU * u : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)
      ∈ AdelicBox.integralFiniteAdeles (𝓞 F) F := by
    rw [Units.val_mul, hsUval]
    exact hsu

  have h1 := distribHaarChar_finUnit_of_hasTransversal (sU * u) (hT (sU * u) hsuZ)
  have h2 := distribHaarChar_finUnit_of_hasTransversal sU (hT sU hsZ)
  rw [finUnit_mul, map_mul, NNReal.coe_mul, h2, finprod_norm_mul] at h1
  exact mul_left_cancel₀ (finprod_norm_pos sU).ne' h1

theorem distribHaarChar_eq_placeModulus
    (hT : ∀ y : (FiniteAdeleRing (𝓞 F) F)ˣ,
      (y : FiniteAdeleRing (𝓞 F) F) ∈ AdelicBox.integralFiniteAdeles (𝓞 F) F →
        HasTransversal (y : FiniteAdeleRing (𝓞 F) F))
    (x : (AdeleRing (𝓞 F) F)ˣ) :
    (distribHaarChar (AdeleRing (𝓞 F) F) x : ℝ) = placeModulus F x := by
  conv_lhs => rw [eq_archUnit_mul_finUnit x]
  rw [map_mul, NNReal.coe_mul,
    NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one F (archUnit x) (archUnit_snd x),
    distribHaarChar_finUnit hT]
  simp only [archUnit_fst]
  rfl

end P6B.JE2aHMod
p2m_reactivate "P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B.JE2aHMod P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField.AdelicCountability P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.M4aS4"
p2m_reactivate "P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B.JE2aHMod P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField.AdelicCountability P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.M4aS4"

end
p2m_reactivate "P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B.JE2aHMod P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField.AdelicCountability P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.M4aS4"

end RHMODFold_JE2aHMod3
p2m_reactivate "P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.P6B.JE2aHMod P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.NumberField.AdelicCountability P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.M4aS4"

theorem solution
    (F : Type) [Field F] [NumberField F]
    (a : (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)ˣ) :
    (MeasureTheory.distribHaarChar (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) a : ℝ)
      = (∏ w : NumberField.InfinitePlace F,
            ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F).1 w‖ ^ w.mult)
        * ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
            ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F).2 v‖ :=
  P6B.JE2aHMod.distribHaarChar_eq_placeModulus (P6B.JE2aHMod.hasTransversal F) a

#print axioms solution

end S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
end P2MW
export P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm (solution)
