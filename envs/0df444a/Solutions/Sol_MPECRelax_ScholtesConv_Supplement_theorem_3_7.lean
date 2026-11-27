-- Prove2me | solution 1 for MPECRelax.ScholtesConv.Supplement.theorem_3_7
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:27:11.466262+00:00
-- url     : https://prove2.me/submissions/41ca6b23-a1d5-42ff-a50a-9aadaf0d4cec

import Mathlib
import Definitions.Def_MPECRelax_ScholtesConv_NLP
import Definitions.Def_MPECRelax_ScholtesConv_MPEC
import Definitions.Def_MPECRelax_ScholtesConv_Supplement_CQ
import Definitions.Def_MPECRelax_ScholtesConv_Supplement_KDB

open Filter Topology Set

open MPECRelax
open MPECRelax.ScholtesConv
open MPECRelax.ScholtesConv.Supplement

theorem solution {n m p l : ℕ} (P : MPEC n m p l) (hP : P.IsC1) (xs : E n)
    (hxs : P.Feasible xs) (hLICQ : MPEC_LICQ P xs) :
    ∃ tbar : ℝ, 0 < tbar ∧ ∃ N ∈ 𝓝 xs, ∀ t ∈ Ioo 0 tbar, ∀ x ∈ N,
      (RKDB P t).Feasible x → IsGCQ (RKDB P t) x := by
        classical
        obtain ⟨hf1, hg1, hh1, hG1, hH1⟩ := hP
        obtain ⟨hxg, hxh, hxGH⟩ := hxs
        have hgd : ∀ i, Differentiable ℝ (P.g i) := fun i => (hg1 i).differentiable one_ne_zero
        have hhd : ∀ i, Differentiable ℝ (P.h i) := fun i => (hh1 i).differentiable one_ne_zero
        have hGd : ∀ i, Differentiable ℝ (P.G i) := fun i => (hG1 i).differentiable one_ne_zero
        have hHd : ∀ i, Differentiable ℝ (P.H i) := fun i => (hH1 i).differentiable one_ne_zero
        have hgr : ∀ (f : E n → ℝ) (y z : E n), inner ℝ (gradient f y) z = fderiv ℝ f y z := by
          intro f y z; simp [gradient]
        set Q := P.TNLP xs with hQ
        let ι' := ↥(Q.activeSet xs) ⊕ (Fin p ⊕ ↥(P.I0p xs ∪ P.I00 xs) ⊕ ↥(P.Ip0 xs ∪ P.I00 xs))
        let Fc : ι' → E n → ℝ := Sum.elim (fun i => Q.g i.1) (fun j => Q.h j)
        have hFc1 : ∀ c, ContDiff ℝ 1 (Fc c) := by
          rintro (⟨(i|i|i), _⟩ | (j|i|i))
          · exact hg1 i
          · exact (hH1 i.1).neg
          · exact (hG1 i.1).neg
          · exact hh1 j
          · exact hG1 i.1
          · exact hH1 i.1
        have hLIxs : LinearIndependent ℝ (fun c => gradient (Fc c) xs) := by
          have : (fun c => gradient (Fc c) xs) = Sum.elim (fun i : ↥(Q.activeSet xs) => gradient (Q.g i.1) xs)
              (fun j => gradient (Q.h j) xs) := by
            funext c; rcases c with c | c <;> rfl
          rw [this]; exact hLICQ
        have hLIopen : ∀ᶠ y in 𝓝 xs, LinearIndependent ℝ (fun c => gradient (Fc c) y) := by
          have hcont : Continuous (fun y => fun c => gradient (Fc c) y) := by
            apply continuous_pi; intro c
            have : gradient (Fc c) = fun y => (InnerProductSpace.toDual ℝ (E n)).symm (fderiv ℝ (Fc c) y) := by
              funext y; rfl
            rw [this]
            exact (LinearIsometryEquiv.continuous _).comp ((hFc1 c).continuous_fderiv one_ne_zero)
          exact (isOpen_setOf_linearIndependent.preimage hcont).mem_nhds hLIxs
        have hev : ∀ᶠ q in (𝓝 (0:ℝ)) ×ˢ (𝓝 xs), LinearIndependent ℝ (fun c => gradient (Fc c) q.2) ∧
            (∀ i, P.g i xs < 0 → P.g i q.2 < 0) ∧ (∀ i, 0 < P.G i xs → q.1 < P.G i q.2) ∧
            (∀ i, 0 < P.H i xs → q.1 < P.H i q.2) := by
          rw [← nhds_prod_eq]
          refine ((continuous_snd.tendsto ((0:ℝ), xs)).eventually hLIopen).and (Filter.Eventually.and ?_ (Filter.Eventually.and ?_ ?_))
          · refine eventually_all.2 fun i => eventually_imp_distrib_left.2 fun hi => ?_
            exact ContinuousAt.eventually_lt (f := fun q : ℝ × E n => P.g i q.2) (g := fun _ => (0:ℝ))
              ((hg1 i).continuous.comp continuous_snd).continuousAt continuousAt_const hi
          · refine eventually_all.2 fun i => eventually_imp_distrib_left.2 fun hi => ?_
            exact ContinuousAt.eventually_lt (f := fun q : ℝ × E n => q.1) (g := fun q => P.G i q.2)
              continuous_fst.continuousAt ((hG1 i).continuous.comp continuous_snd).continuousAt hi
          · refine eventually_all.2 fun i => eventually_imp_distrib_left.2 fun hi => ?_
            exact ContinuousAt.eventually_lt (f := fun q : ℝ × E n => q.1) (g := fun q => P.H i q.2)
              continuous_fst.continuousAt ((hH1 i).continuous.comp continuous_snd).continuousAt hi
        obtain ⟨pa, hpa, pb, hpb, hpab⟩ := eventually_prod_iff.1 hev
        obtain ⟨ε, hε, hεpa⟩ := Metric.eventually_nhds_iff.1 hpa
        obtain ⟨N, hNpb, hNo, hxsN⟩ := mem_nhds_iff.1 hpb
        refine ⟨ε, hε, N, hNo.mem_nhds hxsN, ?_⟩
        intro t ht x hxN hfeas
        have hN : ∀ y ∈ N, LinearIndependent ℝ (fun c => gradient (Fc c) y) ∧
            (∀ i, P.g i xs < 0 → P.g i y < 0) ∧ (∀ i, 0 < P.G i xs → t < P.G i y) ∧
            (∀ i, 0 < P.H i xs → t < P.H i y) := by
          intro y hy
          refine hpab (x := t) (y := y) (hεpa ?_) (hNpb hy)
          rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]; exact ht.2
        set X := feasSet (RKDB P t) with hX
        have hTL : ∀ φ : E n → ℝ, DifferentiableAt ℝ φ x → (∀ y ∈ X, φ y ≤ φ x) →
            ∀ d ∈ tangentCone X x, fderiv ℝ φ x d ≤ 0 := by
          intro φ hφ hle d hd
          obtain ⟨xk, τ, hxk, hτ, -, hτ0, hxkx, hlim⟩ := hd
          have h0 : Tendsto (fun k => xk k - x) atTop (𝓝 0) := by
            simpa using hxkx.sub_const x
          have := (hφ.hasFDerivAt.hasFDerivWithinAt (s := univ)).lim (l := atTop)
            (c := fun k => (τ k)⁻¹) h0 (Eventually.of_forall fun k => mem_univ _) hlim
          refine le_of_tendsto this (Eventually.of_forall fun k => ?_)
          simp only [add_sub_cancel, smul_eq_mul]
          exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (hτ k).le) (sub_nonpos.2 (hle _ (hxk k)))
        have hRd : ∀ c, Differentiable ℝ ((RKDB P t).g c) := by
          rintro (i|i|i|i)
          · exact hgd i
          · exact ((hGd i).neg).sub_const t
          · exact ((hHd i).neg).sub_const t
          · exact ((hGd i).sub_const t).mul ((hHd i).sub_const t)
        have TsubL : tangentCone X x ⊆ linCone (RKDB P t) x := by
          intro d hd
          refine ⟨fun c hc => ?_, fun j => ?_⟩
          · rw [hgr]
            refine hTL _ (hRd c x) (fun y hy => ?_) d hd
            have hc' : (RKDB P t).g c x = 0 := hc
            rw [hc']; exact hy.1 c
          · rw [hgr]
            apply le_antisymm
            · exact hTL _ (hhd j x) (fun y hy => by
                have h1 : P.h j y = 0 := hy.2 j
                have h2 : P.h j x = 0 := hfeas.2 j
                linarith) d hd
            · have := hTL (fun y => - P.h j y) (hhd j x).neg (fun y hy => by
                have h1 : P.h j y = 0 := hy.2 j
                have h2 : P.h j x = 0 := hfeas.2 j
                linarith) d hd
              simp only [fderiv_fun_neg, ContinuousLinearMap.neg_apply] at this
              show 0 ≤ fderiv ℝ (P.h j) x d
              linarith
        refine Subset.antisymm ?_ (fun v hv d hd => hv d (TsubL hd))
        intro v hv d hd
        have hLIx := (hN x hxN).1
        have hsurj : ∀ u : ι' → ℝ, ∃ z : E n, ∀ c, fderiv ℝ (Fc c) x z = u c := by
          let M : E n →ₗ[ℝ] (ι' → ℝ) := LinearMap.pi (fun c => (fderiv ℝ (Fc c) x : E n →ₗ[ℝ] ℝ))
          have hM : LinearMap.range M = ⊤ := by
            by_contra hne
            obtain ⟨f, hf0, hfle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
            set lam : ι' → ℝ := fun c => f (fun j => if c = j then 1 else 0) with hlam
            have hfz : ∀ z : E n, f (M z) = inner ℝ (∑ c, lam c • gradient (Fc c) x) z := by
              intro z
              rw [LinearMap.pi_apply_eq_sum_univ f (M z), sum_inner]
              refine Finset.sum_congr rfl fun c _ => ?_
              rw [real_inner_smul_left, hgr]
              show fderiv ℝ (Fc c) x z • lam c = _
              rw [smul_eq_mul, mul_comm]
            have hsum : ∑ c, lam c • gradient (Fc c) x = 0 := by
              have := hfz (∑ c, lam c • gradient (Fc c) x)
              rw [hfle ⟨_, rfl⟩] at this
              exact inner_self_eq_zero.1 this.symm
            have hlam0 : ∀ c, lam c = 0 := Fintype.linearIndependent_iff.1 hLIx lam hsum
            apply hf0
            apply LinearMap.ext; intro w
            rw [LinearMap.pi_apply_eq_sum_univ f w]
            simp only [LinearMap.zero_apply]
            refine Finset.sum_eq_zero fun c _ => ?_
            have := hlam0 c
            simp only [hlam] at this
            rw [this, smul_zero]
          intro u
          obtain ⟨z, hz⟩ := (LinearMap.range_eq_top.1 hM) u
          exact ⟨z, fun c => by rw [← hz]; rfl⟩
        have KEY : ∀ u : ι' → ℝ, (∀ᶠ r in 𝓝[>] (0:ℝ), ∀ y ∈ N, (∀ c, Fc c y = Fc c x + r * u c) →
            (RKDB P t).Feasible y) → ∀ z : E n, (∀ c, fderiv ℝ (Fc c) x z = u c) → z ∈ tangentCone X x := by
          intro u hu z hz
          let Fh : E n × ℝ → (ι' → ℝ) := fun q c => Fc c q.1 - q.2 * u c
          let f' : E n × ℝ →L[ℝ] (ι' → ℝ) := ContinuousLinearMap.pi (fun c =>
            (fderiv ℝ (Fc c) x).comp (ContinuousLinearMap.fst ℝ (E n) ℝ) - u c • ContinuousLinearMap.snd ℝ (E n) ℝ)
          have hFh : HasStrictFDerivAt Fh f' (x, 0) := by
            apply hasStrictFDerivAt_pi.2; intro c
            have h1 : HasStrictFDerivAt (Fc c) (fderiv ℝ (Fc c) x) x :=
              ((hFc1 c).contDiffAt).hasStrictFDerivAt one_ne_zero
            exact (h1.comp (x, 0) hasStrictFDerivAt_fst).sub (hasStrictFDerivAt_snd.mul_const (u c))
          have hf's : LinearMap.range (f' : E n × ℝ →ₗ[ℝ] (ι' → ℝ)) = ⊤ := by
            rw [LinearMap.range_eq_top]; intro w
            obtain ⟨z', hz'⟩ := hsurj w
            refine ⟨(z', 0), ?_⟩
            funext c; simp [f', hz']
          have hk0 : ((z, 1) : E n × ℝ) ∈ LinearMap.ker (f' : E n × ℝ →ₗ[ℝ] (ι' → ℝ)) := by
            rw [LinearMap.mem_ker]; funext c; simp [f', hz]
          let k0 : ↥(LinearMap.ker (f' : E n × ℝ →ₗ[ℝ] (ι' → ℝ))) := ⟨(z, 1), hk0⟩
          let φ := hFh.implicitFunction Fh f' hf's (Fh (x, 0))
          let γ : ℝ → E n × ℝ := fun s => φ (s • k0)
          have hγ0 : γ 0 = (x, 0) := by
            simp only [γ, zero_smul]; exact hFh.implicitFunction_apply_image hf's
          have hγd : HasDerivAt γ (z, 1) 0 := by
            have h1 := (hFh.to_implicitFunction hf's).hasFDerivAt
            have h2 : HasDerivAt (fun s : ℝ => s • k0) k0 0 := by
              simpa using (hasDerivAt_id (0:ℝ)).smul_const k0
            rw [← zero_smul ℝ k0] at h1
            exact h1.comp_hasDerivAt (0:ℝ) h2
          have hγeq : ∀ᶠ s in 𝓝 (0:ℝ), Fh (γ s) = Fh (x, 0) := by
            have := hFh.map_implicitFunction_eq hf's
            have ht' : Tendsto (fun s : ℝ => (Fh (x, 0), s • k0)) (𝓝 0) (𝓝 (Fh (x, 0), 0)) := by
              refine tendsto_const_nhds.prodMk_nhds ?_
              have : Tendsto (fun s : ℝ => s • k0) (𝓝 0) (𝓝 ((0:ℝ) • k0)) :=
                (continuous_id.smul continuous_const).tendsto 0
              simpa using this
            exact ht'.eventually this
          have hslope := hasDerivAt_iff_tendsto_slope_zero.1 hγd
          simp only [zero_add, hγ0] at hslope
          let σ : ℕ → ℝ := fun k => 1 / ((k:ℝ) + 1)
          have hσpos : ∀ k, 0 < σ k := fun k => by positivity
          have hσ : Tendsto σ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
          have hσne : Tendsto σ atTop (𝓝[≠] 0) :=
            tendsto_nhdsWithin_iff.2 ⟨hσ, Eventually.of_forall fun k => (hσpos k).ne'⟩
          have hA := hslope.comp hσne
          have hA1 : Tendsto (fun k => (σ k)⁻¹ • ((γ (σ k)).1 - x)) atTop (𝓝 z) := by
            have := (continuous_fst.tendsto _).comp hA
            simpa [Function.comp_def] using this
          have hA2 : Tendsto (fun k => (σ k)⁻¹ * (γ (σ k)).2) atTop (𝓝 1) := by
            have := (continuous_snd.tendsto _).comp hA
            simpa [Function.comp_def] using this
          have hγc : Tendsto γ (𝓝 0) (𝓝 (x, 0)) := hγ0 ▸ hγd.continuousAt.tendsto
          have hB := hγc.comp hσ
          have e1 : ∀ᶠ k in atTop, 0 < (γ (σ k)).2 := by
            filter_upwards [hA2.eventually (lt_mem_nhds one_pos)] with k hk
            have := hσpos k
            have h3 : (γ (σ k)).2 = σ k * ((σ k)⁻¹ * (γ (σ k)).2) := by field_simp
            rw [h3]; positivity
          have e2 : ∀ᶠ k in atTop, (γ (σ k)).1 ∈ N :=
            ((continuous_fst.tendsto _).comp hB).eventually (hNo.mem_nhds hxN)
          have e3 : ∀ᶠ k in atTop, Fh (γ (σ k)) = Fh (x, 0) := hσ.eventually hγeq
          have e4 : ∀ᶠ k in atTop, ∀ y ∈ N, (∀ c, Fc c y = Fc c x + (γ (σ k)).2 * u c) →
              (RKDB P t).Feasible y := by
            have : Tendsto (fun k => (γ (σ k)).2) atTop (𝓝[>] 0) :=
              tendsto_nhdsWithin_iff.2 ⟨by simpa [Function.comp_def] using (continuous_snd.tendsto _).comp hB, e1⟩
            exact this.eventually hu
          have eF : ∀ᶠ k in atTop, (RKDB P t).Feasible (γ (σ k)).1 := by
            filter_upwards [e2, e3, e4] with k h2 h3 h4
            refine h4 _ h2 fun c => ?_
            have := congrFun h3 c
            simp only [Fh] at this
            linarith
          obtain ⟨K, hK⟩ := eventually_atTop.1 eF
          refine ⟨fun k => (γ (σ (k + K))).1, fun k => σ (k + K), fun k => hK _ (by omega),
            fun k => hσpos _, ?_, (tendsto_add_atTop_iff_nat K).2 hσ,
            (tendsto_add_atTop_iff_nat K).2 (by simpa [Function.comp_def] using (continuous_fst.tendsto _).comp hB),
            (tendsto_add_atTop_iff_nat K).2 hA1⟩
          intro a b hab
          simp only [σ]
          apply one_div_le_one_div_of_le (by positivity)
          have : (a:ℝ) ≤ b := by exact_mod_cast hab
          push_cast; linarith
        have hmemG : ∀ i, P.G i xs = 0 → i ∈ P.I0p xs ∪ P.I00 xs := by
          intro i hi
          rcases (hxGH i).2.1.lt_or_eq with h | h
          · exact Or.inl ⟨hi, h⟩
          · exact Or.inr ⟨hi, h.symm⟩
        have hmemH : ∀ i, P.H i xs = 0 → i ∈ P.Ip0 xs ∪ P.I00 xs := by
          intro i hi
          rcases (hxGH i).1.lt_or_eq with h | h
          · exact Or.inl ⟨h, hi⟩
          · exact Or.inr ⟨h.symm, hi⟩
        let U : (Fin m → ℝ) → (Fin l → ℝ) → (Fin l → ℝ) → ι' → ℝ := fun ag aG aH =>
          Sum.elim (fun c => Sum.elim ag (fun _ => 0) c.1)
            (Sum.elim (fun _ => 0) (Sum.elim (fun c => aG c.1) (fun c => aH c.1)))
        have GEN : ∀ ag aG aH, (∀ᶠ r in 𝓝[>] (0:ℝ),
            (∀ i, P.g i xs = 0 → P.g i x + r * ag i ≤ 0) ∧
            (∀ i, P.G i xs = 0 → -t ≤ P.G i x + r * aG i) ∧
            (∀ i, P.H i xs = 0 → -t ≤ P.H i x + r * aH i) ∧
            (∀ i, P.G i xs = 0 → 0 < P.H i xs → P.G i x + r * aG i ≤ t) ∧
            (∀ i, P.H i xs = 0 → 0 < P.G i xs → P.H i x + r * aH i ≤ t) ∧
            (∀ i, P.G i xs = 0 → P.H i xs = 0 → (P.G i x + r * aG i - t) * (P.H i x + r * aH i - t) ≤ 0)) →
            ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ y ∈ N, (∀ c, Fc c y = Fc c x + r * U ag aG aH c) →
              (RKDB P t).Feasible y := by
          intro ag aG aH hC
          filter_upwards [hC] with r ⟨C1, C2, C3, C4, C5, C6⟩ y hy hval
          have hNy := hN y hy
          have vG : ∀ i (hi : P.G i xs = 0), P.G i y = P.G i x + r * aG i := fun i hi =>
            hval (Sum.inr (Sum.inr (Sum.inl ⟨i, hmemG i hi⟩)))
          have vH : ∀ i (hi : P.H i xs = 0), P.H i y = P.H i x + r * aH i := fun i hi =>
            hval (Sum.inr (Sum.inr (Sum.inr ⟨i, hmemH i hi⟩)))
          refine ⟨?_, fun j => ?_⟩
          · rintro (i|i|i|i)
            · show P.g i y ≤ 0
              by_cases hi : P.g i xs = 0
              · have : P.g i y = P.g i x + r * ag i := hval (Sum.inl ⟨Sum.inl i, hi⟩)
                rw [this]; exact C1 i hi
              · exact (hNy.2.1 i (lt_of_le_of_ne (hxg i) hi)).le
            · show -P.G i y - t ≤ 0
              by_cases hi : P.G i xs = 0
              · linarith [C2 i hi, vG i hi]
              · have := hNy.2.2.1 i (lt_of_le_of_ne (hxGH i).1 (Ne.symm hi)); linarith [ht.1]
            · show -P.H i y - t ≤ 0
              by_cases hi : P.H i xs = 0
              · linarith [C3 i hi, vH i hi]
              · have := hNy.2.2.2 i (lt_of_le_of_ne (hxGH i).2.1 (Ne.symm hi)); linarith [ht.1]
            · show (P.G i y - t) * (P.H i y - t) ≤ 0
              by_cases hG0 : P.G i xs = 0 <;> by_cases hH0 : P.H i xs = 0
              · rw [vG i hG0, vH i hH0]; exact C6 i hG0 hH0
              · have hHp := lt_of_le_of_ne (hxGH i).2.1 (Ne.symm hH0)
                have h1 := hNy.2.2.2 i hHp
                have h2 := C4 i hG0 hHp
                rw [vG i hG0]; nlinarith
              · have hGp := lt_of_le_of_ne (hxGH i).1 (Ne.symm hG0)
                have h1 := hNy.2.2.1 i hGp
                have h2 := C5 i hH0 hGp
                rw [vH i hH0]; nlinarith
              · exfalso
                rcases mul_eq_zero.1 (hxGH i).2.2 with h | h
                · exact hG0 h
                · exact hH0 h
          · have h1 : P.h j y = P.h j x + r * 0 := hval (Sum.inr (Sum.inl j))
            have h2 : P.h j x = 0 := hfeas.2 j
            show P.h j y = 0
            rw [h1, h2]; ring
        obtain ⟨hdg, hdh⟩ := hd
        have fg : ∀ i, P.g i x ≤ 0 := fun i => hfeas.1 (Sum.inl i)
        have fG : ∀ i, -P.G i x - t ≤ 0 := fun i => hfeas.1 (Sum.inr (Sum.inl i))
        have fH : ∀ i, -P.H i x - t ≤ 0 := fun i => hfeas.1 (Sum.inr (Sum.inr (Sum.inl i)))
        have fΦ : ∀ i, (P.G i x - t) * (P.H i x - t) ≤ 0 := fun i => hfeas.1 (Sum.inr (Sum.inr (Sum.inr i)))
        set ag : Fin m → ℝ := fun i => fderiv ℝ (P.g i) x d with hag
        set aG : Fin l → ℝ := fun i => fderiv ℝ (P.G i) x d with haG
        set aH : Fin l → ℝ := fun i => fderiv ℝ (P.H i) x d with haH
        have Lg : ∀ i, P.g i x = 0 → ag i ≤ 0 := fun i hi => by
          have := hdg (Sum.inl i) hi; rwa [hgr] at this
        have Lh : ∀ j, fderiv ℝ (P.h j) x d = 0 := fun j => by
          have := hdh j; rwa [hgr] at this
        have LG : ∀ i, P.G i x = -t → 0 ≤ aG i := fun i hi => by
          have := hdg (Sum.inr (Sum.inl i)) (show -P.G i x - t = 0 by linarith)
          rw [hgr] at this
          change fderiv ℝ (fun y => -P.G i y - t) x d ≤ 0 at this
          have e : HasFDerivAt (fun y => -P.G i y - t) (-fderiv ℝ (P.G i) x) x :=
            (hGd i x).hasFDerivAt.neg.sub_const t
          rw [e.fderiv] at this
          simp only [neg_apply] at this
          show 0 ≤ fderiv ℝ (P.G i) x d; linarith
        have LH : ∀ i, P.H i x = -t → 0 ≤ aH i := fun i hi => by
          have := hdg (Sum.inr (Sum.inr (Sum.inl i))) (show -P.H i x - t = 0 by linarith)
          rw [hgr] at this
          change fderiv ℝ (fun y => -P.H i y - t) x d ≤ 0 at this
          have e : HasFDerivAt (fun y => -P.H i y - t) (-fderiv ℝ (P.H i) x) x :=
            (hHd i x).hasFDerivAt.neg.sub_const t
          rw [e.fderiv] at this
          simp only [neg_apply] at this
          show 0 ≤ fderiv ℝ (P.H i) x d; linarith
        have LΦ : ∀ i, (P.G i x - t) * (P.H i x - t) = 0 →
            (P.H i x - t) * aG i + (P.G i x - t) * aH i ≤ 0 := fun i hi => by
          have := hdg (Sum.inr (Sum.inr (Sum.inr i))) hi
          rw [hgr] at this
          change fderiv ℝ (fun y => (P.G i y - t) * (P.H i y - t)) x d ≤ 0 at this
          have e : HasFDerivAt (fun y => (P.G i y - t) * (P.H i y - t))
              ((P.G i x - t) • fderiv ℝ (P.H i) x + (P.H i x - t) • fderiv ℝ (P.G i) x) x :=
            ((hGd i x).hasFDerivAt.sub_const t).mul ((hHd i x).hasFDerivAt.sub_const t)
          rw [e.fderiv] at this
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at this
          show (P.H i x - t) * fderiv ℝ (P.G i) x d + (P.G i x - t) * fderiv ℝ (P.H i) x d ≤ 0
          linarith
        have hsmf : ∀ f : ℝ → ℝ, Continuous f → f 0 < 0 → ∀ᶠ r in 𝓝[>] (0:ℝ), f r < 0 :=
          fun f hf h0 => nhdsWithin_le_nhds (hf.continuousAt.eventually_lt (g := fun _ => (0:ℝ))
            continuousAt_const h0)
        have hpos : ∀ᶠ r in 𝓝[>] (0:ℝ), 0 < r := self_mem_nhdsWithin
        -- the two pieces
        have G1 := GEN ag aG 0 (by
          refine Filter.Eventually.and ?_ (Filter.Eventually.and ?_ (Filter.Eventually.and ?_
            (Filter.Eventually.and ?_ (Filter.Eventually.and ?_ ?_))))
          · refine eventually_all.2 fun i => ?_
            by_cases hx0 : P.g i x = 0
            · filter_upwards [hpos] with r hr _
              have := Lg i hx0; rw [hx0]; nlinarith
            · have hlt := lt_of_le_of_ne (fg i) hx0
              filter_upwards [hsmf (fun r => P.g i x + r * ag i) (by fun_prop) (by simpa using hlt)]
                with r hr _ using hr.le
          · refine eventually_all.2 fun i => ?_
            by_cases hx0 : P.G i x = -t
            · filter_upwards [hpos] with r hr _
              have := LG i hx0; nlinarith
            · have hlt : -t < P.G i x := lt_of_le_of_ne (by linarith [fG i]) (Ne.symm hx0)
              filter_upwards [hsmf (fun r => -t - (P.G i x + r * aG i)) (by fun_prop) (by simpa using hlt)]
                with r hr _ using by linarith
          · exact Eventually.of_forall fun r i _ => by simp; linarith [fH i]
          · refine eventually_all.2 fun i => ?_
            by_cases hHp : 0 < P.H i xs
            · have h1 := (hN x hxN).2.2.2 i hHp
              have hGle : P.G i x ≤ t := by nlinarith [fΦ i]
              by_cases hx0 : P.G i x = t
              · filter_upwards [hpos] with r hr _ _
                have := LΦ i (by rw [hx0]; ring); rw [hx0] at this
                have : aG i ≤ 0 := by nlinarith
                nlinarith
              · have hlt := lt_of_le_of_ne hGle hx0
                filter_upwards [hsmf (fun r => (P.G i x + r * aG i) - t) (by fun_prop) (by simpa using hlt)]
                  with r hr _ _ using by linarith
            · exact Eventually.of_forall fun r _ h => absurd h hHp
          · refine Eventually.of_forall fun r i _ hGp => ?_
            have h1 := (hN x hxN).2.2.1 i hGp
            simp; nlinarith [fΦ i]
          · refine eventually_all.2 fun i => ?_
            by_cases hHt : P.H i x = t
            · exact Eventually.of_forall fun r _ _ => by simp [hHt]
            · by_cases hGt : P.G i x = t
              · filter_upwards [hpos] with r hr _ _
                have := LΦ i (by rw [hGt]; ring); rw [hGt] at this ⊢
                simp; nlinarith
              · have hneg : (P.G i x - t) * (P.H i x - t) < 0 :=
                  lt_of_le_of_ne (fΦ i) (mul_ne_zero (sub_ne_zero.2 hGt) (sub_ne_zero.2 hHt))
                filter_upwards [hsmf (fun r => (P.G i x + r * aG i - t) * (P.H i x - t)) (by fun_prop)
                  (by simpa using hneg)] with r hr _ _
                simp; linarith)
        have G2 := GEN 0 0 aH (by
          refine Filter.Eventually.and ?_ (Filter.Eventually.and ?_ (Filter.Eventually.and ?_
            (Filter.Eventually.and ?_ (Filter.Eventually.and ?_ ?_))))
          · exact Eventually.of_forall fun r i _ => by simp; exact fg i
          · exact Eventually.of_forall fun r i _ => by simp; linarith [fG i]
          · refine eventually_all.2 fun i => ?_
            by_cases hx0 : P.H i x = -t
            · filter_upwards [hpos] with r hr _
              have := LH i hx0; nlinarith
            · have hlt : -t < P.H i x := lt_of_le_of_ne (by linarith [fH i]) (Ne.symm hx0)
              filter_upwards [hsmf (fun r => -t - (P.H i x + r * aH i)) (by fun_prop) (by simpa using hlt)]
                with r hr _ using by linarith
          · refine Eventually.of_forall fun r i _ hHp => ?_
            have h1 := (hN x hxN).2.2.2 i hHp
            simp; nlinarith [fΦ i]
          · refine eventually_all.2 fun i => ?_
            by_cases hGp : 0 < P.G i xs
            · have h1 := (hN x hxN).2.2.1 i hGp
              have hHle : P.H i x ≤ t := by nlinarith [fΦ i]
              by_cases hx0 : P.H i x = t
              · filter_upwards [hpos] with r hr _ _
                have := LΦ i (by rw [hx0]; ring); rw [hx0] at this
                have : aH i ≤ 0 := by nlinarith
                nlinarith
              · have hlt := lt_of_le_of_ne hHle hx0
                filter_upwards [hsmf (fun r => (P.H i x + r * aH i) - t) (by fun_prop) (by simpa using hlt)]
                  with r hr _ _ using by linarith
            · exact Eventually.of_forall fun r _ h => absurd h hGp
          · refine eventually_all.2 fun i => ?_
            by_cases hGt : P.G i x = t
            · exact Eventually.of_forall fun r _ _ => by simp [hGt]
            · by_cases hHt : P.H i x = t
              · filter_upwards [hpos] with r hr _ _
                have := LΦ i (by rw [hHt]; ring); rw [hHt] at this ⊢
                simp; nlinarith
              · have hneg : (P.G i x - t) * (P.H i x - t) < 0 :=
                  lt_of_le_of_ne (fΦ i) (mul_ne_zero (sub_ne_zero.2 hGt) (sub_ne_zero.2 hHt))
                filter_upwards [hsmf (fun r => (P.G i x - t) * (P.H i x + r * aH i - t)) (by fun_prop)
                  (by simpa using hneg)] with r hr _ _
                simp; linarith)
        obtain ⟨d1, hd1⟩ := hsurj (U ag aG 0)
        have hD : ∀ c, fderiv ℝ (Fc c) x d = U ag aG 0 c + U 0 0 aH c := by
          rintro (⟨(i|i|i), hc⟩ | (j|i|i))
          · simp [U, ag]; rfl
          · exfalso
            have h1 : -P.H i.1 xs = 0 := hc
            have := i.2.2; linarith
          · exfalso
            have h1 : -P.G i.1 xs = 0 := hc
            have := i.2.1; linarith
          · simp [U]; exact Lh j
          · simp [U, aG]; rfl
          · simp [U, aH]; rfl
        have hd2 : ∀ c, fderiv ℝ (Fc c) x (d - d1) = U 0 0 aH c := by
          intro c; rw [map_sub, hD c, hd1 c]; ring
        have T1 := KEY _ G1 d1 hd1
        have T2 := KEY _ G2 (d - d1) hd2
        have := hv d1 T1
        have := hv (d - d1) T2
        have e : d = d1 + (d - d1) := by abel
        rw [e, inner_add_right]; linarith
