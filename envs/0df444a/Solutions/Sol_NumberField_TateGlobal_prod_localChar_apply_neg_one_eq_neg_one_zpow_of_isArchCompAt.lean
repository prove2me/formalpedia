-- Prove2me | solution 1 for NumberField.TateGlobal.prod_localChar_apply_neg_one_eq_neg_one_zpow_of_isArchCompAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7e3b0343-29d1-57aa-95a4-6cadd17388f4

import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_prod_localChar_apply_neg_one_eq_neg_one_zpow_of_isArchCompAt

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField P2MW.S_NumberField_TateGlobal_prod_localChar_apply_neg_one_eq_neg_one_zpow_of_isArchCompAt.NumberField NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_prod_localChar_apply_neg_one_eq_neg_one_zpow_of_isArchCompAt.NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse"

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing place InfinitePlace AdeleRing AdelicLevel.finIncl AdelicLevel.localUnit AdelicLevel.localUnit_apply_self AdelicLevel.localUnit_apply_of_ne TateGlobal.archUnitHom TateGlobal.archUnitHom_apply AdelicVolume.archCentralUnit_fst_self"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "localChar archUnitHom IsUnramifiedCharAt archUnitHom_apply"
namespace NegOneOffSet
p2m_open "NumberField.TateGlobal NumberField"

variable (S : Finset (HeightOneSpectrum (𝓞 ℚ)))

private noncomputable def unitIdeleOff (T : Finset {w : HeightOneSpectrum (𝓞 ℚ) // w ∉ S}) :
    (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  ∏ x ∈ T, NumberField.AdelicLevel.localUnit (𝓞 ℚ) ℚ x.1 (-1)

private theorem val_unitIdeleOff_apply (T : Finset {w : HeightOneSpectrum (𝓞 ℚ) // w ∉ S})
    (w : HeightOneSpectrum (𝓞 ℚ)) :
    ((unitIdeleOff S T : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w =
      ∏ x ∈ T, ((NumberField.AdelicLevel.localUnit (𝓞 ℚ) ℚ x.1 (-1) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        FiniteAdeleRing (𝓞 ℚ) ℚ) w := by
  unfold unitIdeleOff
  rw [Units.coe_prod]
  exact map_prod (RestrictedProduct.evalMonoidHom _ w) _ _

private theorem val_unitIdeleOff_apply_of_mem (T : Finset {w : HeightOneSpectrum (𝓞 ℚ) // w ∉ S})
    (x : {w : HeightOneSpectrum (𝓞 ℚ) // w ∉ S}) (hx : x ∈ T) :
    ((unitIdeleOff S T : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) x.1 = -1 := by
  rw [val_unitIdeleOff_apply, Finset.prod_eq_single x]
  · rw [NumberField.AdelicLevel.localUnit_apply_self, Units.val_neg, Units.val_one]
  · intro y _ hyx
    exact NumberField.AdelicLevel.localUnit_apply_of_ne (𝓞 ℚ) ℚ y.1 (-1) fun h => hyx (Subtype.ext h.symm)
  · intro h
    exact absurd hx h

private theorem val_unitIdeleOff_apply_of_forall_ne (T : Finset {w : HeightOneSpectrum (𝓞 ℚ) // w ∉ S})
    (w : HeightOneSpectrum (𝓞 ℚ)) (hw : ∀ x ∈ T, w ≠ x.1) :
    ((unitIdeleOff S T : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w = 1 := by
  rw [val_unitIdeleOff_apply]
  exact Finset.prod_eq_one fun x hx => NumberField.AdelicLevel.localUnit_apply_of_ne (𝓞 ℚ) ℚ x.1 (-1) (hw x hx)

private theorem val_unitIdeleOff_apply_mem (T : Finset {w : HeightOneSpectrum (𝓞 ℚ) // w ∉ S})
    (w : HeightOneSpectrum (𝓞 ℚ)) :
    ((unitIdeleOff S T : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w ∈ w.adicCompletionIntegers ℚ := by
  by_cases h : ∃ x ∈ T, w = x.1
  · obtain ⟨x, hx, rfl⟩ := h
    rw [val_unitIdeleOff_apply_of_mem S T x hx]
    exact neg_mem (one_mem _)
  · push Not at h
    rw [val_unitIdeleOff_apply_of_forall_ne S T w h]
    exact one_mem _

private theorem unitIdeleOff_mul_self (T : Finset {w : HeightOneSpectrum (𝓞 ℚ) // w ∉ S}) :
    unitIdeleOff S T * unitIdeleOff S T = 1 := by
  unfold unitIdeleOff
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun x _ => ?_
  rw [← map_mul, neg_one_mul, neg_neg, map_one]

private theorem inv_unitIdeleOff (T : Finset {w : HeightOneSpectrum (𝓞 ℚ) // w ∉ S}) :
    (unitIdeleOff S T)⁻¹ = unitIdeleOff S T :=
  inv_eq_of_mul_eq_one_right (unitIdeleOff_mul_self S T)

open scoped Classical in

private noncomputable def limitVal : FiniteAdeleRing (𝓞 ℚ) ℚ :=
  ⟨fun w => if w ∈ S then 1 else -1,
    Filter.Eventually.of_forall fun w => by
      dsimp only
      split_ifs
      · exact one_mem _
      · exact neg_mem (one_mem _)⟩

open scoped Classical in
private theorem limitVal_apply_of_mem {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ∈ S) : limitVal S w = 1 := by
  show (if w ∈ S then (1 : w.adicCompletion ℚ) else -1) = 1
  simp [hw]

open scoped Classical in
private theorem limitVal_apply_of_not_mem {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ∉ S) : limitVal S w = -1 := by
  show (if w ∈ S then (1 : w.adicCompletion ℚ) else -1) = -1
  simp [hw]

private theorem limitVal_apply_mem (w : HeightOneSpectrum (𝓞 ℚ)) : limitVal S w ∈ w.adicCompletionIntegers ℚ := by
  by_cases hw : w ∈ S
  · rw [limitVal_apply_of_mem S hw]
    exact one_mem _
  · rw [limitVal_apply_of_not_mem S hw]
    exact neg_mem (one_mem _)

private theorem limitVal_mul_self : limitVal S * limitVal S = 1 := by
  refine Subtype.ext (funext fun w => ?_)
  show limitVal S w * limitVal S w = 1
  by_cases hw : w ∈ S
  · rw [limitVal_apply_of_mem S hw, mul_one]
  · rw [limitVal_apply_of_not_mem S hw, neg_one_mul, neg_neg]

private noncomputable def limitUnit : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  ⟨limitVal S, limitVal S, limitVal_mul_self S, limitVal_mul_self S⟩

private theorem tendsto_val_unitIdeleOff :
    Filter.Tendsto (fun T : Finset {w : HeightOneSpectrum (𝓞 ℚ) // w ∉ S} =>
        ((unitIdeleOff S T : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ))
      Filter.atTop (nhds (limitVal S)) := by
  have hT : ∀ T : Finset {w : HeightOneSpectrum (𝓞 ℚ) // w ∉ S}, ∃ y,
      RestrictedProduct.structureMap _ _ _ y =
        ((unitIdeleOff S T : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    fun T => RestrictedProduct.exists_structureMap_eq_of_forall _ _ (val_unitIdeleOff_apply_mem S T)
  choose y hy using hT
  obtain ⟨yL, hyL⟩ := RestrictedProduct.exists_structureMap_eq_of_forall _ _ (limitVal_apply_mem S)
  have hfun : (fun T : Finset {w : HeightOneSpectrum (𝓞 ℚ) // w ∉ S} =>
      ((unitIdeleOff S T : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)) =
        fun T => RestrictedProduct.structureMap _ _ _ (y T) := funext fun T => (hy T).symm
  rw [hfun, ← hyL]
  refine (RestrictedProduct.isEmbedding_structureMap.continuous.tendsto yL).comp (tendsto_pi_nhds.mpr fun w => ?_)
  have hcoe : ∀ T, ((y T w : w.adicCompletion ℚ)) =
      ((unitIdeleOff S T : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w := fun T => by
    rw [← hy T]
    rfl
  have hcoeL : ((yL w : w.adicCompletion ℚ)) = limitVal S w := by
    rw [← hyL]
    rfl
  by_cases hw : w ∈ S
  · refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun T => ?_)
    apply Subtype.ext
    rw [hcoeL, hcoe T, limitVal_apply_of_mem S hw, val_unitIdeleOff_apply_of_forall_ne]
    intro x _ hx
    exact x.2 (hx ▸ hw)
  · refine tendsto_const_nhds.congr'
      ((Filter.eventually_ge_atTop {(⟨w, hw⟩ : {w : HeightOneSpectrum (𝓞 ℚ) // w ∉ S})}).mono
      fun T hT => ?_)
    apply Subtype.ext
    rw [hcoeL, hcoe T, limitVal_apply_of_not_mem S hw,
      val_unitIdeleOff_apply_of_mem S T ⟨w, hw⟩ (hT (Finset.mem_singleton_self _))]

private theorem tendsto_unitIdeleOff :
    Filter.Tendsto (fun T : Finset {w : HeightOneSpectrum (𝓞 ℚ) // w ∉ S} => unitIdeleOff S T) Filter.atTop
      (nhds (limitUnit S)) := by
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  have hval := tendsto_val_unitIdeleOff S
  have hinv : Filter.Tendsto (fun T : Finset {w : HeightOneSpectrum (𝓞 ℚ) // w ∉ S} =>
      MulOpposite.op (((unitIdeleOff S T)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ))
      Filter.atTop
        (nhds (MulOpposite.op (((limitUnit S)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ))) := by
    simp only [inv_unitIdeleOff]
    exact (MulOpposite.continuous_op.tendsto _).comp hval
  exact hval.prodMk_nhds hinv

private theorem continuous_apply_map_finIncl (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hσc : Continuous σ) :
    Continuous fun x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ => σ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 ℚ) ℚ) x) := by
  refine hσc.comp (Units.continuous_iff.mpr ⟨?_, ?_⟩)
  · show Continuous fun x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ => ((1 : InfiniteAdeleRing ℚ), (x : FiniteAdeleRing (𝓞 ℚ) ℚ))
    exact continuous_const.prodMk Units.continuous_val
  · show Continuous fun x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ =>
      ((1 : InfiniteAdeleRing ℚ), ((x⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ))
    exact continuous_const.prodMk Units.continuous_coe_inv

private theorem apply_unitIdeleOff_eq_one (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hunr : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S → IsUnramifiedCharAt σ w)
    (T : Finset {w : HeightOneSpectrum (𝓞 ℚ) // w ∉ S}) :
    σ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 ℚ) ℚ) (unitIdeleOff S T)) = 1 := by
  unfold unitIdeleOff
  rw [map_prod, map_prod]
  refine Finset.prod_eq_one fun x _ => ?_
  have h1 : (((-1 : (x.1.adicCompletion ℚ)ˣ)) : x.1.adicCompletion ℚ) ∈ x.1.adicCompletionIntegers ℚ := by
    rw [Units.val_neg, Units.val_one]
    exact neg_mem (one_mem _)
  have h2 : ((((-1 : (x.1.adicCompletion ℚ)ˣ))⁻¹ : (x.1.adicCompletion ℚ)ˣ) : x.1.adicCompletion ℚ) ∈
      x.1.adicCompletionIntegers ℚ := by
    rw [inv_neg_one]
    exact h1
  exact hunr x.1 x.2 (-1) h1 h2

private theorem apply_limitUnit_eq_one (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hσc : Continuous σ)
    (hunr : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S → IsUnramifiedCharAt σ w) :
    σ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 ℚ) ℚ) (limitUnit S)) = 1 := by
  have h1 : Filter.Tendsto (fun T : Finset {w : HeightOneSpectrum (𝓞 ℚ) // w ∉ S} =>
      σ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 ℚ) ℚ) (unitIdeleOff S T))) Filter.atTop
        (nhds (σ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 ℚ) ℚ) (limitUnit S)))) :=
    ((continuous_apply_map_finIncl σ hσc).tendsto _).comp (tendsto_unitIdeleOff S)
  have h2 : Filter.Tendsto (fun T : Finset {w : HeightOneSpectrum (𝓞 ℚ) // w ∉ S} =>
      σ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 ℚ) ℚ) (unitIdeleOff S T))) Filter.atTop (nhds 1) := by
    simp only [apply_unitIdeleOff_eq_one S σ hunr]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique h1 h2

private theorem apply_archEmbed_neg_one_eq (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (t : ℂ) (a : ℤ)
    (harch : ∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ σ w t a) :
    ((σ (NumberField.TateGlobal.archUnitHom Rat.infinitePlace (-1)) : ℂˣ) : ℂ) = (-1 : ℂ) ^ a := by
  have h := harch Rat.infinitePlace Rat.isReal_infinitePlace (-1)
  rw [Units.val_neg, Units.val_one, norm_neg, norm_one, Complex.ofReal_one, Complex.one_cpow, one_mul, map_neg,
    map_one, div_one] at h
  exact h

private noncomputable def unitIdeleOn : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  ∏ p ∈ S, NumberField.AdelicLevel.localUnit (𝓞 ℚ) ℚ p (-1)

private theorem val_unitIdeleOn_apply (w : HeightOneSpectrum (𝓞 ℚ)) :
    ((unitIdeleOn S : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w =
      ∏ p ∈ S, ((NumberField.AdelicLevel.localUnit (𝓞 ℚ) ℚ p (-1) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        FiniteAdeleRing (𝓞 ℚ) ℚ) w := by
  unfold unitIdeleOn
  rw [Units.coe_prod]
  exact map_prod (RestrictedProduct.evalMonoidHom _ w) _ _

private theorem neg_one_eq_mul_mul_limitUnit :
    (-1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ) =
      NumberField.TateGlobal.archUnitHom Rat.infinitePlace (-1) *
          Units.map (NumberField.AdelicLevel.finIncl (𝓞 ℚ) ℚ) (unitIdeleOn S) *
        Units.map (NumberField.AdelicLevel.finIncl (𝓞 ℚ) ℚ) (limitUnit S) := by
  refine Units.ext ?_
  rw [Units.val_neg, Units.val_one, Units.val_mul, Units.val_mul]
  refine Prod.ext ?_ ?_
  · show (-1 : InfiniteAdeleRing ℚ) =
      ((NumberField.TateGlobal.archUnitHom Rat.infinitePlace (-1) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
        AdeleRing (𝓞 ℚ) ℚ).1 * 1 * 1
    rw [mul_one, mul_one]
    funext p
    obtain rfl : p = Rat.infinitePlace := Subsingleton.elim _ _
    rw [NumberField.TateGlobal.archUnitHom_apply, NumberField.AdelicVolume.archCentralUnit_fst_self, Units.val_neg,
      Units.val_one]
    rfl
  · show (-1 : FiniteAdeleRing (𝓞 ℚ) ℚ) =
      1 * ((unitIdeleOn S : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) * limitVal S
    rw [one_mul]
    refine Subtype.ext (funext fun w => ?_)
    show (-1 : w.adicCompletion ℚ) =
      ((unitIdeleOn S : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w * limitVal S w
    rw [val_unitIdeleOn_apply]
    by_cases hw : w ∈ S
    · rw [limitVal_apply_of_mem S hw, mul_one, Finset.prod_eq_single w]
      · rw [NumberField.AdelicLevel.localUnit_apply_self, Units.val_neg, Units.val_one]
      · intro p _ hpw
        exact NumberField.AdelicLevel.localUnit_apply_of_ne (𝓞 ℚ) ℚ p (-1) (Ne.symm hpw)
      · intro h
        exact absurd hw h
    · rw [limitVal_apply_of_not_mem S hw, Finset.prod_eq_one fun p hp => ?_, one_mul]
      exact NumberField.AdelicLevel.localUnit_apply_of_ne (𝓞 ℚ) ℚ p (-1) fun h => hw (h ▸ hp)

end NumberField.TateGlobal.NegOneOffSet

open NumberField.TateGlobal.NegOneOffSet in

theorem solution
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hσ : IsIdeleClassChar (𝓞 ℚ) ℚ σ) (hσc : Continuous σ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hunr : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S → IsUnramifiedCharAt σ w)
    (t : ℂ) (a : ℤ) (harch : ∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ σ w t a) :
    ∏ w ∈ S, ((localChar σ w (-1) : ℂˣ) : ℂ) = (-1 : ℂ) ^ a := by
  have hprin : σ (-1) = 1 := by simpa only [Units.map_neg_one] using hσ (-1)
  rw [NumberField.TateGlobal.NegOneOffSet.neg_one_eq_mul_mul_limitUnit S, map_mul, map_mul,
    NumberField.TateGlobal.NegOneOffSet.apply_limitUnit_eq_one S σ hσc hunr, mul_one] at hprin

  have hS : σ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 ℚ) ℚ)
      (NumberField.TateGlobal.NegOneOffSet.unitIdeleOn S)) = ∏ w ∈ S, localChar σ w (-1) := by
    unfold NumberField.TateGlobal.NegOneOffSet.unitIdeleOn
    rw [map_prod, map_prod]
    rfl
  have harch1 := NumberField.TateGlobal.NegOneOffSet.apply_archEmbed_neg_one_eq σ t a harch
  have h := congrArg (fun u : ℂˣ => (u : ℂ)) hprin
  simp only [Units.val_mul, Units.val_one, hS, harch1, Units.coe_prod] at h

  have hsq : (-1 : ℂ) ^ a * (-1 : ℂ) ^ a = 1 := by
    rw [← mul_zpow, neg_one_mul, neg_neg, one_zpow]
  calc ∏ w ∈ S, ((localChar σ w (-1) : ℂˣ) : ℂ)
      = (-1 : ℂ) ^ a * ((-1 : ℂ) ^ a * ∏ w ∈ S, ((localChar σ w (-1) : ℂˣ) : ℂ)) := by
        rw [← mul_assoc, hsq, one_mul]
    _ = (-1 : ℂ) ^ a := by rw [h, mul_one]

end S_NumberField_TateGlobal_prod_localChar_apply_neg_one_eq_neg_one_zpow_of_isArchCompAt
end P2MW
export P2MW.S_NumberField_TateGlobal_prod_localChar_apply_neg_one_eq_neg_one_zpow_of_isArchCompAt (solution)
