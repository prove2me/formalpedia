-- Prove2me | solution 1 for NumberField.TateGlobal.eq_one_of_forall_isUnramifiedCharAt_of_fst_eq_one_of_mem_adicCompletionIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a8d83193-aa37-5e3a-aeb1-4ee0e0d0f297

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_eq_one_of_forall_isUnramifiedCharAt_of_fst_eq_one_of_mem_adicCompletionIntegers

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm
open NumberField.AdelicLevel Filter Topology
open scoped RestrictedProduct Classical

noncomputable section

namespace C3d

variable {K : Type} [Field K] [NumberField K]

abbrev ιv (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  (Units.map (finIncl (𝓞 K) K)).comp (localUnit (𝓞 K) K v)

theorem localChar_eq (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    NumberField.TateGlobal.localChar χ v t = χ (ιv K v t) := rfl

abbrev sM (K : Type) [Field K] [NumberField K]
    (y : ∀ w : HeightOneSpectrum (𝓞 K), ↥(w.adicCompletionIntegers K)) : FiniteAdeleRing (𝓞 K) K :=
  RestrictedProduct.structureMap (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
    (fun w => ((w.adicCompletionIntegers K) : Set (w.adicCompletion K))) cofinite y

theorem sM_apply (y : ∀ w : HeightOneSpectrum (𝓞 K), ↥(w.adicCompletionIntegers K)) (w : HeightOneSpectrum (𝓞 K)) :
    (sM K y) w = (y w : w.adicCompletion K) := rfl

theorem continuous_sM : Continuous (sM K) :=
  (RestrictedProduct.isEmbedding_structureMap (R := fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
    (A := fun w => ((w.adicCompletionIntegers K) : Set (w.adicCompletion K))) (𝓕 := cofinite)).continuous

section Family

def yS (t : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ)
    (ht : ∀ v, ((t v : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K) (S : Finset (HeightOneSpectrum (𝓞 K))) : ∀ w : HeightOneSpectrum (𝓞 K), ↥(w.adicCompletionIntegers K) :=
  fun w => if w ∈ S then ⟨(t w : w.adicCompletion K), ht w⟩ else 1

def yT (t : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ)
    (ht : ∀ v, ((t v : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K) : ∀ w : HeightOneSpectrum (𝓞 K), ↥(w.adicCompletionIntegers K) := fun w => ⟨(t w : w.adicCompletion K), ht w⟩

theorem coe_yS (t : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ)
    (ht : ∀ v, ((t v : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K) (S : Finset (HeightOneSpectrum (𝓞 K))) (w : HeightOneSpectrum (𝓞 K)) :
    ((yS t ht S w : ↥(w.adicCompletionIntegers K)) : w.adicCompletion K) =
      if w ∈ S then (t w : w.adicCompletion K) else 1 := by
  unfold yS
  split_ifs <;> rfl

def zS (t : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ) (S : Finset (HeightOneSpectrum (𝓞 K))) : (AdeleRing (𝓞 K) K)ˣ := ∏ v ∈ S, ιv K v (t v)

theorem coe_zS (t : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ)
    (ht : ∀ v, ((t v : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ((zS t S : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = ((1 : InfiniteAdeleRing K), sM K (yS t ht S)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [zS, Finset.prod_empty, Units.val_one]
    refine Prod.ext rfl ?_
    apply RestrictedProduct.ext
    intro w
    show (1 : FiniteAdeleRing (𝓞 K) K) w = (sM K (yS t ht ∅)) w
    rw [sM_apply, coe_yS]
    simp only [Finset.notMem_empty, if_false]
    rfl
  | insert a S ha ih =>
    rw [zS, Finset.prod_insert ha, Units.val_mul, ← zS, ih]
    refine Prod.ext ?_ ?_
    · show (finIncl (𝓞 K) K _).1 * 1 = 1
      rw [finIncl_apply_fst, one_mul]
    · apply RestrictedProduct.ext
      intro w
      show ((localUnit (𝓞 K) K a (t a) : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w *
        (sM K (yS t ht S)) w = (sM K (yS t ht (insert a S))) w
      rw [sM_apply, sM_apply, coe_yS, coe_yS]
      by_cases hw : w = a
      · subst hw
        rw [localUnit_apply_self, if_neg ha, if_pos (Finset.mem_insert_self _ _), mul_one]
      · rw [localUnit_apply_of_ne (𝓞 K) K a (t a) hw, one_mul]
        simp only [Finset.mem_insert, hw, false_or]

theorem tendsto_sM_yS (t : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ)
    (ht : ∀ v, ((t v : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K) : Tendsto (fun S => sM K (yS t ht S)) atTop (𝓝 (sM K (yT t ht))) := by
  refine (continuous_sM.tendsto _).comp ?_
  rw [tendsto_pi_nhds]
  intro w
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ({w} : Finset (HeightOneSpectrum (𝓞 K)))] with S hS
  have hw : w ∈ S := hS (Finset.mem_singleton_self w)
  unfold yS yT
  rw [if_pos hw]

theorem tendsto_coe_zS (t : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ)
    (ht : ∀ v, ((t v : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K) : Tendsto (fun S => ((zS t S : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) atTop
    (𝓝 ((1 : InfiniteAdeleRing K), sM K (yT t ht))) := by
  have e : (fun S => ((zS t S : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) =
      fun S => ((1 : InfiniteAdeleRing K), sM K (yS t ht S)) := funext fun S => coe_zS t ht S
  rw [e]
  exact Tendsto.prodMk_nhds tendsto_const_nhds (tendsto_sM_yS t ht)

end Family

end C3d

open C3d in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ))
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), NumberField.TateGlobal.IsUnramifiedCharAt χ v)
    (z : (AdeleRing (𝓞 K) K)ˣ) (hz : ((z : AdeleRing (𝓞 K) K)).1 = 1)
    (hzf : ∀ v : HeightOneSpectrum (𝓞 K),
      ((z : AdeleRing (𝓞 K) K)).2 v ∈ v.adicCompletionIntegers K ∧
      (((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v ∈ v.adicCompletionIntegers K) :
    χ z = 1 := by
  classical

  have hmul : ∀ v : HeightOneSpectrum (𝓞 K),
      ((z : AdeleRing (𝓞 K) K)).2 v * (((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v = 1 := fun v => by
    have := congrArg (fun a : AdeleRing (𝓞 K) K => a.2 v) z.mul_inv
    exact this
  have hmul' : ∀ v : HeightOneSpectrum (𝓞 K),
      (((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v * ((z : AdeleRing (𝓞 K) K)).2 v = 1 := fun v => by
    rw [mul_comm]; exact hmul v
  let u : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ := fun v =>
    ⟨((z : AdeleRing (𝓞 K) K)).2 v, (((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v, hmul v, hmul' v⟩
  have hu : ∀ v, ((u v : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K := fun v => (hzf v).1
  have hui : ∀ v, ((u⁻¹ v : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K := fun v => (hzf v).2

  have hχS : ∀ S : Finset (HeightOneSpectrum (𝓞 K)), ((χ (zS u S) : ℂˣ) : ℂ) = 1 := by
    intro S
    rw [zS, map_prod, Finset.prod_eq_one fun v _ => ?_, Units.val_one]
    rw [← localChar_eq]
    exact hram v (u v) (hzf v).1 (hzf v).2

  have hzval : ((z : AdeleRing (𝓞 K) K)) = ((1 : InfiniteAdeleRing K), sM K (yT u hu)) := by
    refine Prod.ext hz ?_
    apply RestrictedProduct.ext
    intro w
    rfl
  have hz1 : (((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 = 1 := by
    have h := congrArg Prod.fst z.mul_inv
    change ((z : AdeleRing (𝓞 K) K)).1 * (((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 = 1 at h
    rw [hz, one_mul] at h
    exact h
  have hzinv : (((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) = ((1 : InfiniteAdeleRing K), sM K (yT u⁻¹ hui)) := by
    refine Prod.ext hz1 ?_
    apply RestrictedProduct.ext
    intro w
    rfl
  have hinvS : ∀ S, (zS u S)⁻¹ = zS u⁻¹ S := fun S => by
    simp only [zS, ← Finset.prod_inv_distrib, ← map_inv, Pi.inv_apply]
  have T1 : Tendsto (fun S => ((zS u S : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) atTop (𝓝 (z : AdeleRing (𝓞 K) K)) := by
    rw [hzval]; exact tendsto_coe_zS u hu
  have T2 : Tendsto (fun S => (((zS u S)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) atTop
      (𝓝 (((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) := by
    rw [hzinv]
    simp only [hinvS]
    exact tendsto_coe_zS u⁻¹ hui
  have T : Tendsto (fun S => zS u S) atTop (𝓝 z) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    show Tendsto (fun S => (((zS u S : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K),
      MulOpposite.op (((zS u S)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) atTop
      (𝓝 (((z : AdeleRing (𝓞 K) K)), MulOpposite.op (((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))))
    exact Tendsto.prodMk_nhds T1 ((MulOpposite.continuous_op.tendsto _).comp T2)

  have hlim : Tendsto (fun S => ((χ (zS u S) : ℂˣ) : ℂ)) atTop (𝓝 ((χ z : ℂˣ) : ℂ)) := (hχc.tendsto z).comp T
  simp only [hχS] at hlim
  exact Units.val_eq_one.1 (tendsto_nhds_unique tendsto_const_nhds hlim).symm

end
end S_NumberField_TateGlobal_eq_one_of_forall_isUnramifiedCharAt_of_fst_eq_one_of_mem_adicCompletionIntegers
end P2MW
export P2MW.S_NumberField_TateGlobal_eq_one_of_forall_isUnramifiedCharAt_of_fst_eq_one_of_mem_adicCompletionIntegers (solution)
