-- Prove2me | solution 1 for JointMixND.QuadOT.Supplement.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:23:56.351426+00:00
-- url     : https://prove2.me/submissions/3c57b9c8-cf75-4e48-8f41-85260dc1bad3

import Mathlib
import Definitions.Def_JointMixND_QuadOT_Basic
import Definitions.Def_JointMixND_QuadOT_Supplement_Dependence

open MeasureTheory ProbabilityTheory

open JointMixND
open JointMixND.QuadOT
open JointMixND.QuadOT.Supplement

theorem solution {n : ℕ} (P : Measure (Fin n → ℝ)) [IsProbabilityMeasure P]
    (hJM : IsJointMix P)
    (ha : ∀ A : Finset (Fin n),
      CondIndepFun (MeasurableSpace.comap (sumOver A) inferInstance)
        (measurable_sumOver A).comap_le (restrictTo A) (restrictTo Aᶜ) P)
    (hb : ∀ (A : Finset (Fin n)) (f : (A → ℝ) → ℝ), Monotone f →
      Integrable (fun x => f (restrictTo A x)) P →
      ∃ (g : ℝ → ℝ) (T : Set ℝ), (∀ᵐ x ∂P, sumOver A x ∈ T) ∧ MonotoneOn g T ∧
        P[fun x => f (restrictTo A x) | MeasurableSpace.comap (sumOver A) inferInstance]
          =ᵐ[P] fun x => g (sumOver A x)) :
    IsNA P := by
      classical
      have hnegative : ∀ (U V : (Fin n → ℝ) → ℝ), Integrable U P → Integrable V P →
          Integrable (fun x => U x * V x) P →
          (∀ᵐ x ∂P, ∀ᵐ y ∂P, (U x - U y) * (V x - V y) ≤ 0) →
          (∫ x, U x * V x ∂P) - (∫ x, U x ∂P) * (∫ x, V x ∂P) ≤ 0 := by
        intro U V hU hV hUV hpair
        have hinner (x : Fin n → ℝ) :
            (∫ y, (U x - U y) * (V x - V y) ∂P) =
              U x * V x - U x * (∫ y, V y ∂P) - V x * (∫ y, U y ∂P) +
                (∫ y, U y * V y ∂P) := by
          calc
            _ = ∫ y, ((U x * V x - U x * V y) - V x * U y) + U y * V y ∂P := by
              congr 1; ext y; ring
            _ = _ := by
              rw [integral_add, integral_sub, integral_sub]
              · simp [integral_const_mul]
              · exact integrable_const _
              · exact hV.const_mul _
              · exact (integrable_const _).sub (hV.const_mul _)
              · exact hU.const_mul _
              · exact ((integrable_const _).sub (hV.const_mul _)).sub (hU.const_mul _)
              · exact hUV
        have hh : ∀ᵐ x ∂P,
            U x * V x - U x * (∫ y, V y ∂P) - V x * (∫ y, U y ∂P) +
              (∫ y, U y * V y ∂P) ≤ 0 := by
          filter_upwards [hpair] with x hx
          rw [← hinner x]
          exact integral_nonpos_of_ae hx
        have ho := integral_nonpos_of_ae hh
        rw [integral_add, integral_sub, integral_sub] at ho
        rotate_left
        · exact hUV
        · exact hU.mul_const _
        · exact hUV.sub (hU.mul_const _)
        · exact hV.mul_const _
        · exact (hUV.sub (hU.mul_const _)).sub (hV.mul_const _)
        · exact integrable_const _
        simp only [integral_mul_const, integral_const, probReal_univ, one_smul] at ho
        nlinarith
      obtain ⟨c, hc⟩ := hJM
      have hsum (A : Finset (Fin n)) : ∀ᵐ x ∂P, sumOver A x + sumOver Aᶜ x = c := by
        filter_upwards [hc] with x hx
        simpa only [sumOver, Finset.sum_add_sum_compl] using hx
      have hceq (A : Finset (Fin n)) (H : (Fin n → ℝ) → ℝ) (hH : Integrable H P) :
          P[H | MeasurableSpace.comap (sumOver A) inferInstance] =ᵐ[P]
            P[H | MeasurableSpace.comap (sumOver Aᶜ) inferInstance] := by
        let mA := MeasurableSpace.comap (sumOver A) inferInstance
        let mC := MeasurableSpace.comap (sumOver Aᶜ) inferInstance
        let : MeasurableSpace (Fin n → ℝ) := MeasurableSpace.pi
        have hmA : mA ≤ MeasurableSpace.pi := (measurable_sumOver A).comap_le
        have hmC : mC ≤ MeasurableSpace.pi := (measurable_sumOver Aᶜ).comap_le
        obtain ⟨v, hv, heq⟩ :=
          (show StronglyMeasurable[mC] (P[H | mC]) from stronglyMeasurable_condExp).exists_eq_measurable_comp
        have hrep : P[H | mC] =ᵐ[P] fun x => v (c - sumOver A x) := by
          filter_upwards [hsum A] with x hx
          rw [heq]
          dsimp [Function.comp_def]
          congr 1
          linarith
        have hmeas : AEStronglyMeasurable[mA] (P[H | mC]) P := by
          refine (hv.comp_measurable ?_).aestronglyMeasurable.congr hrep.symm
          exact measurable_const.sub (measurable_iff_comap_le.mpr le_rfl)
        refine (ae_eq_condExp_of_forall_setIntegral_eq hmA hH
          (fun s _ _ => integrable_condExp.integrableOn) ?_ hmeas).symm
        intro s hs htop
        obtain ⟨t, ht, rfl⟩ := hs
        let s' := (fun x => c - sumOver Aᶜ x) ⁻¹' t
        have hs' : MeasurableSet[mC] s' :=
          (measurable_const.sub (measurable_iff_comap_le.mpr le_rfl)) ht
        have he : (sumOver A ⁻¹' t) =ᵐ[P] s' := by
          filter_upwards [hsum A] with x hx
          change (sumOver A x ∈ t) = (c - sumOver Aᶜ x ∈ t)
          congr 1
          linarith
        calc
          _ = ∫ x in s', (P[H | mC]) x ∂P := setIntegral_congr_set he
          _ = ∫ x in s', H x ∂P := setIntegral_condExp hmC hH hs'
          _ = _ := setIntegral_congr_set he.symm
      have hproduct (A : Finset (Fin n)) (f : (A → ℝ) → ℝ) (g : (↥(Aᶜ) → ℝ) → ℝ)
          (hF : Integrable (fun x => f (restrictTo A x)) P)
          (hG : Integrable (fun x => g (restrictTo Aᶜ x)) P)
          (hFG : Integrable (fun x => f (restrictTo A x) * g (restrictTo Aᶜ x)) P) :
          P[fun x => f (restrictTo A x) * g (restrictTo Aᶜ x) |
              MeasurableSpace.comap (sumOver A) inferInstance] =ᵐ[P]
          fun x => (P[fun y => f (restrictTo A y) |
              MeasurableSpace.comap (sumOver A) inferInstance]) x *
            (P[fun y => g (restrictTo Aᶜ y) |
              MeasurableSpace.comap (sumOver A) inferInstance]) x := by
        let e : (Fin n → ℝ) ≃ᵐ ((A → ℝ) × (↥(Aᶜ) → ℝ)) :=
          { toFun := fun x => (restrictTo A x, restrictTo Aᶜ x)
            invFun := fun p i => if hi : i ∈ A then p.1 ⟨i, hi⟩ else p.2 ⟨i, by simpa using hi⟩
            left_inv := by intro x; ext i; dsimp [restrictTo]; split_ifs <;> rfl
            right_inv := by
              intro p
              apply Prod.ext <;> ext i <;> dsimp [restrictTo]
              · simp [i.property]
              · simp [Finset.mem_compl.mp i.property]
            measurable_toFun := (measurable_restrictTo A).prodMk (measurable_restrictTo Aᶜ)
            measurable_invFun := by
              apply measurable_pi_lambda
              intro i
              by_cases hi : i ∈ A
              · simpa [hi, Function.comp_def] using (measurable_pi_apply (⟨i, hi⟩ : A)).comp measurable_fst
              · simpa [hi, Function.comp_def] using
                  (measurable_pi_apply (⟨i, by simpa using hi⟩ : ↥(Aᶜ))).comp measurable_snd }
        let mA := MeasurableSpace.comap (sumOver A) inferInstance
        let : MeasurableSpace (Fin n → ℝ) := MeasurableSpace.pi
        have hmA : mA ≤ MeasurableSpace.pi := (measurable_sumOver A).comap_le
        let K := condExpKernel P mA
        have hmap : ∀ᵐ x ∂P, (K x).map e =
            ((K x).map (restrictTo A)).prod ((K x).map (restrictTo Aᶜ)) := by
          have hh := (Kernel.indepFun_iff_compProd_map_prod_eq_compProd_prod_map_map
            (measurable_restrictTo A) (measurable_restrictTo Aᶜ)).mp (ha A)
          have hh' := ae_eq_of_ae_eq_trim (Kernel.ae_eq_of_compProd_eq hh)
          filter_upwards [hh'] with x hx
          change (K.map e) x = ((K.map (restrictTo A)) ×ₖ (K.map (restrictTo Aᶜ))) x at hx
          simpa only [Kernel.map_apply _ e.measurable, Kernel.prod_apply,
            Kernel.map_apply _ (measurable_restrictTo A),
            Kernel.map_apply _ (measurable_restrictTo Aᶜ)] using hx
        have hfactor : ∀ᵐ x ∂P,
            (∫ y, f (restrictTo A y) * g (restrictTo Aᶜ y) ∂K x) =
            (∫ y, f (restrictTo A y) ∂K x) * (∫ y, g (restrictTo Aᶜ y) ∂K x) := by
          filter_upwards [hmap] with x hx
          have : IsProbabilityMeasure ((K x).map (restrictTo A)) :=
            Measure.isProbabilityMeasure_map (measurable_restrictTo A).aemeasurable
          have : IsProbabilityMeasure ((K x).map (restrictTo Aᶜ)) :=
            Measure.isProbabilityMeasure_map (measurable_restrictTo Aᶜ).aemeasurable
          have hf : (∫ y, f (restrictTo A y) ∂K x) = ∫ a, f a ∂(K x).map (restrictTo A) := by
            change (∫ y, f (e y).1 ∂K x) = _
            rw [← integral_map_equiv e (fun p => f p.1), hx, integral_fun_fst]
            simp
          have hg : (∫ y, g (restrictTo Aᶜ y) ∂K x) = ∫ b, g b ∂(K x).map (restrictTo Aᶜ) := by
            change (∫ y, g (e y).2 ∂K x) = _
            rw [← integral_map_equiv e (fun p => g p.2), hx, integral_fun_snd]
            simp
          change (∫ y, f (e y).1 * g (e y).2 ∂K x) = _
          rw [← integral_map_equiv e (fun p => f p.1 * g p.2), hx, integral_prod_mul, hf, hg]
        filter_upwards [hfactor, condExp_ae_eq_integral_condExpKernel hmA hF,
          condExp_ae_eq_integral_condExpKernel hmA hG,
          condExp_ae_eq_integral_condExpKernel hmA hFG] with x hx hfx hgx hfgx
        exact hfgx.trans (hx.trans (congrArg₂ (· * ·) hfx.symm hgx.symm))
      intro A B hAB f g hf hg hF hG
      have hBA (i : B) : (i : Fin n) ∈ Aᶜ := by
        simp only [Finset.mem_compl]
        exact Finset.disjoint_right.mp hAB i.property
      let g' : (↥(Aᶜ) → ℝ) → ℝ := fun y => g (fun i : B => y ⟨i, hBA i⟩)
      have hg' : Monotone g' := by
        intro x y hxy
        apply hg
        intro i
        exact hxy _
      have hG' : MemLp (fun x => g' (restrictTo Aᶜ x)) 2 P := hG
      let F : (Fin n → ℝ) → ℝ := fun x => f (restrictTo A x)
      let G : (Fin n → ℝ) → ℝ := fun x => g' (restrictTo Aᶜ x)
      let mA := MeasurableSpace.comap (sumOver A) inferInstance
      let mC := MeasurableSpace.comap (sumOver Aᶜ) inferInstance
      let : MeasurableSpace (Fin n → ℝ) := MeasurableSpace.pi
      have hmA : mA ≤ MeasurableSpace.pi := (measurable_sumOver A).comap_le
      have hmC : mC ≤ MeasurableSpace.pi := (measurable_sumOver Aᶜ).comap_le
      have hFi : Integrable F P := hF.integrable (by norm_num)
      have hGi : Integrable G P := hG'.integrable (by norm_num)
      let U := P[F | mA]
      let V := P[G | mC]
      have hU : MemLp U 2 P := hF.condExp (by norm_num)
      have hV : MemLp V 2 P := hG'.condExp (by norm_num)
      obtain ⟨u, T, hT, hu, heu⟩ := hb A f hf hFi
      obtain ⟨v, S, hS, hv, hev⟩ := hb Aᶜ g' hg' hGi
      have hpair : ∀ᵐ x ∂P, ∀ᵐ y ∂P, (U x - U y) * (V x - V y) ≤ 0 := by
        filter_upwards [hT, hS, heu, hev, hsum A] with x hxT hxS hxU hxV hxsum
        filter_upwards [hT, hS, heu, hev, hsum A] with y hyT hyS hyU hyV hysum
        change U x = u (sumOver A x) at hxU
        change V x = v (sumOver Aᶜ x) at hxV
        change U y = u (sumOver A y) at hyU
        change V y = v (sumOver Aᶜ y) at hyV
        rw [hxU, hxV, hyU, hyV]
        rcases le_total (sumOver A x) (sumOver A y) with hxy | hyx
        · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hu hxT hyT hxy))
            (sub_nonneg.mpr (hv hyS hxS (by linarith)))
        · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hu hyT hxT hyx))
            (sub_nonpos.mpr (hv hxS hyS (by linarith)))
      have hi : (∫ x, F x * G x ∂P) = ∫ x, U x * V x ∂P := by
        rw [← integral_condExp hmA (f := fun x => F x * G x)]
        apply integral_congr_ae
        have hp := hproduct A f g' hFi hGi (hF.integrable_mul hG')
        have he := hceq A G hGi
        filter_upwards [hp, he] with x hx hex
        exact hx.trans (congrArg (U x * ·) hex)
      change covariance F G P ≤ 0
      rw [covariance_eq_sub hF hG']
      change (∫ x, F x * G x ∂P) - (∫ x, F x ∂P) * (∫ x, G x ∂P) ≤ 0
      rw [hi, ← integral_condExp hmA (f := F), ← integral_condExp hmC (f := G)]
      exact hnegative U V (hU.integrable (by norm_num)) (hV.integrable (by norm_num))
        (hU.integrable_mul hV) hpair
