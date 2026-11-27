-- Prove2me | solution 1 for MPECRelax.ScholtesConv.Supplement.theorem_3_11
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:27:37.566437+00:00
-- url     : https://prove2.me/submissions/abe55680-4171-44ad-8ec4-029a27eeed19

import Mathlib
import Definitions.Def_MPECRelax_ScholtesConv_NLP
import Definitions.Def_MPECRelax_ScholtesConv_MPEC
import Definitions.Def_MPECRelax_ScholtesConv_Supplement_CQ
import Definitions.Def_MPECRelax_ScholtesConv_Supplement_SU

open Filter Topology Set

open MPECRelax
open MPECRelax.ScholtesConv
open MPECRelax.ScholtesConv.Supplement

theorem solution {n m p l : ℕ} (P : MPEC n m p l) (hP : P.IsC1)
    (θ : ℝ → ℝ) (hθ : IsSUTheta θ) (xs : E n)
    (hxs : P.Feasible xs) (hLICQ : MPEC_LICQ P xs) :
    ∃ N ∈ 𝓝 xs, ∃ tbar : ℝ, 0 < tbar ∧ ∀ t ∈ Ioo 0 tbar, ∀ x ∈ N,
      (RSU P θ t).Feasible x → IsACQ (RSU P θ t) x := by
        classical
        obtain ⟨hfC, hgC, hhC, hGC, hHC⟩ := hP
        have hgr : ∀ (c : E n → ℝ) (y d : E n), inner ℝ (gradient c y) d = fderiv ℝ c y d := by
          intro c y d; simp [gradient]
        have hϕ : ∀ t : ℝ, 0 < t → (∀ a, DifferentiableAt ℝ (fun a => phiSU θ a t) a) ∧
            (∀ a b, phiSU θ a t + deriv (fun a => phiSU θ a t) a * (b - a) ≤ phiSU θ b t) ∧
            (∀ a, a < -t → deriv (fun a => phiSU θ a t) a = -1) ∧
            (∀ a, t < a → deriv (fun a => phiSU θ a t) a = 1) ∧
            (∀ a, |a| < t → phiSU θ a t ≤ t) := by
          intro t ht
          obtain ⟨hC, hm1, hp1, hdm1, hdp1, -, -, hpos⟩ := hθ
          set D := derivWithin θ (Icc (-1) 1) with hDdef
          have hU : UniqueDiffOn ℝ (Icc (-1:ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
          have hF1 : ∀ u ∈ Icc (-1:ℝ) 1, HasDerivWithinAt θ (D u) (Icc (-1) 1) u := fun u hu =>
            ((hC.differentiableOn (by norm_num)) u hu).hasDerivWithinAt
          have hD1 : ContDiffOn ℝ 1 D (Icc (-1) 1) := hC.derivWithin hU (by norm_num)
          have hDmono : MonotoneOn D (Icc (-1) 1) := by
            apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hD1.continuousOn
            · rw [interior_Icc]
              exact (hD1.differentiableOn (by norm_num)).mono Ioo_subset_Icc_self
            · rw [interior_Icc]
              intro x hx
              have h2 := hpos x hx
              rw [iteratedDerivWithin_succ, iteratedDerivWithin_one] at h2
              rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
              exact h2.le
          have hDb : ∀ u ∈ Icc (-1:ℝ) 1, -1 ≤ D u ∧ D u ≤ 1 := by
            intro u hu
            constructor
            · rw [← hdm1]; exact hDmono ⟨le_refl _, by norm_num⟩ hu hu.1
            · rw [← hdp1]; exact hDmono hu ⟨by norm_num, le_refl _⟩ hu.2
          set ϕ := fun a => phiSU θ a t with hϕdef
          have hEq : ∀ x ∈ Icc (-t) t, ϕ x = t * θ (x / t) := by
            intro x hx
            simp only [hϕdef, phiSU]
            by_cases h : t ≤ |x|
            · rw [if_pos h]
              rcases le_or_gt 0 x with h0 | h0
              · rw [abs_of_nonneg h0] at h ⊢
                have : x = t := le_antisymm hx.2 h
                subst this; rw [div_self ht.ne', hp1]; ring
              · rw [abs_of_neg h0] at h ⊢
                have : x = -t := by linarith [hx.1]
                subst this; rw [neg_div, div_self ht.ne', hm1]; ring
            · rw [if_neg h]
          have hθc : ∀ x ∈ Icc (-t) t, HasDerivWithinAt (fun x => t * θ (x / t)) (D (x / t)) (Icc (-t) t) x := by
            intro x hx
            have hu : x / t ∈ Icc (-1:ℝ) 1 := by
              constructor
              · rw [le_div_iff₀ ht]; linarith [hx.1]
              · rw [div_le_iff₀ ht]; linarith [hx.2]
            have hmap : MapsTo (fun x : ℝ => x / t) (Icc (-t) t) (Icc (-1) 1) := by
              intro z hz
              constructor
              · rw [le_div_iff₀ ht]; linarith [hz.1]
              · rw [div_le_iff₀ ht]; linarith [hz.2]
            have h1 : HasDerivWithinAt (fun x : ℝ => x / t) (1 / t) (Icc (-t) t) x :=
              (hasDerivAt_id x).div_const t |>.hasDerivWithinAt
            have h2 := (hF1 _ hu).comp x h1 hmap
            have h3 := h2.const_mul t
            exact h3.congr_deriv (by field_simp)
          let g : ℝ → ℝ := fun a => if a ≤ -t then -1 else if a < t then D (a / t) else 1
          have hg : ∀ a, HasDerivAt ϕ (g a) a := by
            intro a
            rcases lt_trichotomy a (-t) with h | h | h
            · have hga : g a = -1 := by simp [g, h.le]
              rw [hga]
              have : ϕ =ᶠ[𝓝 a] fun x => -x := by
                filter_upwards [gt_mem_nhds h] with x hx
                have : t ≤ |x| := by rw [abs_of_neg (by linarith)]; linarith
                simp only [hϕdef, phiSU, if_pos this, abs_of_neg (show x < 0 by linarith)]
              exact (hasDerivAt_neg a).congr_of_eventuallyEq this
            · have hga : g a = -1 := by simp [g, h]
              rw [hga, h]
              have hR : HasDerivWithinAt ϕ (-1) (Ici (-t)) (-t) := by
                have := hθc (-t) ⟨le_refl _, by linarith⟩
                rw [neg_div, div_self ht.ne', hdm1] at this
                exact (this.congr (fun x hx => hEq x hx) (hEq (-t) ⟨le_refl _, by linarith⟩)).mono_of_mem_nhdsWithin
                  (Icc_mem_nhdsGE (by linarith))
              have hL : HasDerivWithinAt ϕ (-1) (Iic (-t)) (-t) := by
                have := (hasDerivAt_neg (-t)).hasDerivWithinAt (s := Iic (-t))
                refine this.congr (fun x hx => ?_) ?_
                · have hx' : x ≤ -t := hx
                  have : t ≤ |x| := by rw [abs_of_neg (by linarith)]; linarith
                  simp only [hϕdef, phiSU, if_pos this, abs_of_neg (show x < 0 by linarith)]
                · have : t ≤ |-t| := by rw [abs_neg, abs_of_pos ht]
                  simp only [hϕdef, phiSU, if_pos this, abs_neg, abs_of_pos ht, neg_neg]
              have := hL.union hR
              rw [Iic_union_Ici, hasDerivWithinAt_univ] at this
              exact this
            · rcases lt_trichotomy a t with h' | h' | h'
              · have hga : g a = D (a / t) := by simp [g, h', not_le.2 h]
                rw [hga]
                have hI : Icc (-t) t ∈ 𝓝 a := Icc_mem_nhds h h'
                have := ((hθc a (mem_of_mem_nhds hI)).hasDerivAt hI)
                exact this.congr_of_eventuallyEq (Filter.mem_of_superset hI (fun x hx => hEq x hx))
              · have hga : g a = 1 := by simp [g, h', not_le.2 (show -t < t by linarith)]
                rw [hga, h']
                have hL : HasDerivWithinAt ϕ 1 (Iic t) t := by
                  have := hθc t ⟨by linarith, le_refl t⟩
                  rw [div_self ht.ne', hdp1] at this
                  exact (this.congr (fun x hx => hEq x hx) (hEq t ⟨by linarith, le_refl t⟩)).mono_of_mem_nhdsWithin
                    (Icc_mem_nhdsLE (by linarith))
                have hR : HasDerivWithinAt ϕ 1 (Ici t) t := by
                  have := (hasDerivAt_id t).hasDerivWithinAt (s := Ici t)
                  refine this.congr (fun x hx => ?_) ?_
                  · have hx' : t ≤ x := hx
                    have : t ≤ |x| := by rw [abs_of_pos (by linarith)]; linarith
                    simp only [hϕdef, phiSU, if_pos this, abs_of_pos (show 0 < x by linarith), id]
                  · have : t ≤ |t| := by rw [abs_of_pos ht]
                    simp only [hϕdef, phiSU, if_pos this, abs_of_pos ht, id]
                have := hL.union hR
                rw [Iic_union_Ici, hasDerivWithinAt_univ] at this
                exact this
              · have hga : g a = 1 := by simp [g, not_le.2 (show -t < a by linarith), not_lt.2 h'.le]
                rw [hga]
                have : ϕ =ᶠ[𝓝 a] fun x => x := by
                  filter_upwards [lt_mem_nhds h'] with x hx
                  have : t ≤ |x| := by rw [abs_of_pos (by linarith)]; linarith
                  simp only [hϕdef, phiSU, if_pos this, abs_of_pos (show 0 < x by linarith)]
                exact (hasDerivAt_id a).congr_of_eventuallyEq this
          have hgb : ∀ a, -1 ≤ g a ∧ g a ≤ 1 := by
            intro a
            simp only [g]
            split_ifs with h1 h2
            · norm_num
            · apply hDb
              constructor
              · rw [le_div_iff₀ ht]; linarith
              · rw [div_le_iff₀ ht]; linarith
            · norm_num
          have hgm : Monotone g := by
            intro a b hab
            by_cases h1 : a ≤ -t
            · have : g a = -1 := by simp only [g, if_pos h1]
              rw [this]; exact (hgb b).1
            by_cases h3 : t ≤ b
            · have : g b = 1 := by simp only [g, if_neg (show ¬ b ≤ -t by intro hh; linarith), if_neg (not_lt.2 h3)]
              rw [this]; exact (hgb a).2
            push Not at h1 h3
            have e1 : g a = D (a / t) := by
              simp only [g, if_neg (not_le.2 h1), if_pos (show a < t by linarith)]
            have e2 : g b = D (b / t) := by
              simp only [g, if_neg (show ¬ b ≤ -t by intro hh; linarith), if_pos h3]
            rw [e1, e2]
            have hmem : ∀ x, -t < x → x < t → x / t ∈ Icc (-1:ℝ) 1 := by
              intro x hx1 hx2
              constructor
              · rw [le_div_iff₀ ht]; linarith
              · rw [div_le_iff₀ ht]; linarith
            exact hDmono (hmem a h1 (by linarith)) (hmem b (by linarith) h3)
              (div_le_div_of_nonneg_right hab ht.le)
          have hderiv : ∀ a, deriv ϕ a = g a := fun a => (hg a).deriv
          have htan : ∀ a b, ϕ a + g a * (b - a) ≤ ϕ b := by
            intro a b
            rcases lt_trichotomy a b with h | h | h
            · obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope ϕ g h
                (fun x _ => (hg x).continuousAt.continuousWithinAt) (fun x _ => hg x)
              have h1 : g a ≤ g c := hgm hc.1.le
              rw [eq_div_iff (by linarith)] at hc'
              nlinarith
            · subst h; simp
            · obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope ϕ g h
                (fun x _ => (hg x).continuousAt.continuousWithinAt) (fun x _ => hg x)
              have h1 : g c ≤ g a := hgm hc.2.le
              rw [eq_div_iff (by linarith)] at hc'
              nlinarith
          refine ⟨fun a => (hg a).differentiableAt, fun a b => by rw [hderiv]; exact htan a b,
            fun a ha => by rw [hderiv]; simp [g, ha.le], fun a ha => ?_, fun a ha => ?_⟩
          · rw [hderiv]; simp [g, not_le.2 (show -t < a by linarith), not_lt.2 ha.le]
          · have h1 := htan a t
            have h2 := htan a (-t)
            have e1 : ϕ t = t := by simp [hϕdef, phiSU, abs_of_pos ht]
            have e2 : ϕ (-t) = t := by simp [hϕdef, phiSU, abs_of_pos ht]
            rw [e1] at h1; rw [e2] at h2
            have ha' := abs_lt.1 ha
            change ϕ a ≤ t
            nlinarith
        have hT1 : ∀ (X : Set (E n)) (y d : E n) (c : E n → ℝ), d ∈ tangentCone X y →
            DifferentiableAt ℝ c y → c y = 0 → (∀ z ∈ X, c z ≤ 0) → fderiv ℝ c y d ≤ 0 := by
          intro X y d c hd hc hcy hX
          obtain ⟨xk, τ, hxk, hτ, -, hτ0, hxl, hlim⟩ := hd
          have hτ' : Tendsto τ atTop (𝓝[>] 0) :=
            tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hτ0
              (Eventually.of_forall (fun k => hτ k))
          have hd0 : Tendsto (fun k => xk k - y) atTop (𝓝 0) := by
            have := hxl.sub (tendsto_const_nhds (x := y)); simpa using this
          have h := hc.hasFDerivAt.hasFDerivWithinAt.lim (s := univ) (l := atTop)
            (c := fun k => (τ k)⁻¹) (d := fun k => xk k - y) hd0
            (Eventually.of_forall (fun k => mem_univ _)) hlim
          refine le_of_tendsto' h (fun k => ?_)
          simp only [add_sub_cancel, hcy, sub_zero, smul_eq_mul]
          exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (hτ k).le) (hX _ (hxk k))
        have hT2 : ∀ (X : Set (E n)) (y d : E n) (φ : ℝ → E n), φ 0 = y → HasDerivAt φ d 0 →
            (∀ᶠ s in 𝓝[>] (0:ℝ), φ s ∈ X) → d ∈ tangentCone X y := by
          intro X y d φ hφ0 hφd hev
          obtain ⟨ε, hε, hεs⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hev
          obtain ⟨M, hM⟩ := exists_nat_one_div_lt (show (0:ℝ) < ε from hε)
          let τ : ℕ → ℝ := fun k => 1 / ((k:ℝ) + M + 1)
          have hτpos : ∀ k, 0 < τ k := fun k => by positivity
          have hτlt : ∀ k, τ k < ε := by
            intro k
            refine lt_of_le_of_lt ?_ hM
            apply one_div_le_one_div_of_le (by positivity)
            have : (0:ℝ) ≤ k := Nat.cast_nonneg k
            linarith
          have hτ0 : Tendsto τ atTop (𝓝 0) := by
            have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
            have h2 := this.comp (tendsto_add_atTop_nat M)
            refine h2.congr (fun k => ?_)
            simp only [τ, Function.comp, Nat.cast_add]
          refine ⟨fun k => φ (τ k), τ, fun k => hεs ⟨hτpos k, hτlt k⟩, hτpos, ?_, hτ0, ?_, ?_⟩
          · intro a b hab
            apply one_div_le_one_div_of_le (by positivity)
            have : (a:ℝ) ≤ b := Nat.cast_le.2 hab
            linarith
          · have := hφd.continuousAt.tendsto.comp hτ0
            rw [hφ0] at this; exact this
          · have hs := hasDerivAt_iff_tendsto_slope.1 hφd
            have hτ' : Tendsto τ atTop (𝓝[≠] 0) :=
              tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hτ0
                (Eventually.of_forall (fun k => ne_of_gt (hτpos k)))
            have := hs.comp hτ'
            refine this.congr (fun k => ?_)
            simp [Function.comp, slope_def_module, hφ0]
        have hcurve : ∀ {K : Type} [Fintype K] (B : K → E n → ℝ), (∀ k, ContDiff ℝ 1 (B k)) →
            ∀ y : E n, LinearIndependent ℝ (fun k => gradient (B k) y) → ∀ d : E n,
            ∃ φ : ℝ → E n, ∃ r : ℝ → ℝ, φ 0 = y ∧ HasDerivAt φ d 0 ∧ r 0 = 0 ∧ HasDerivAt r 1 0 ∧
              ∀ᶠ s in 𝓝 (0:ℝ), ∀ k, B k (φ s) = B k y + r s * fderiv ℝ (B k) y d := by
          intro K _ B hB y hLI d
          classical
          let A : E n →L[ℝ] (K → ℝ) := ContinuousLinearMap.pi (fun k => fderiv ℝ (B k) y)
          have hA : ∀ z k, A z k = fderiv ℝ (B k) y z := fun z k => rfl
          have hsurj : LinearMap.range (A : E n →ₗ[ℝ] (K → ℝ)) = ⊤ := by
            by_contra hne
            obtain ⟨c, hc0, hc⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
            let w : K → ℝ := fun k => c (Pi.single k 1)
            have hcv : ∀ v : K → ℝ, c v = ∑ k, w k * v k := by
              intro v
              conv_lhs => rw [show v = ∑ k, v k • Pi.single k (1:ℝ) by
                ext j; simp [Finset.sum_apply, Pi.single_apply]]
              simp [map_sum, w, mul_comm]
            have hz : ∀ z : E n, inner ℝ (∑ k, w k • gradient (B k) y) z = 0 := by
              intro z
              have : c (A z) = 0 := hc ⟨z, rfl⟩
              rw [hcv] at this
              rw [sum_inner]
              simpa [inner_smul_left, gradient, hA] using this
            have h0 : ∑ k, w k • gradient (B k) y = 0 := by
              have := hz (∑ k, w k • gradient (B k) y)
              exact inner_self_eq_zero.1 this
            have hw : ∀ k, w k = 0 := Fintype.linearIndependent_iff.1 hLI w h0
            apply hc0
            exact LinearMap.ext fun v => by rw [hcv]; simp [hw]
          obtain ⟨G0, hG0⟩ := LinearMap.exists_rightInverse_of_surjective _ hsurj
          let G : (K → ℝ) →L[ℝ] E n := LinearMap.toContinuousLinearMap G0
          have hAG : ∀ v, A (G v) = v := fun v => LinearMap.congr_fun hG0 v
          let f : E n → (K → ℝ) := fun z k => B k z
          have hf : HasStrictFDerivAt f A y := by
            rw [hasStrictFDerivAt_pi]
            intro k
            exact ((hB k).contDiffAt).hasStrictFDerivAt (by norm_num)
          let Ψ : E n → E n := fun z => z - G (A z) + G (f z)
          have hΨ : HasStrictFDerivAt Ψ ((ContinuousLinearEquiv.refl ℝ (E n)) : E n →L[ℝ] E n) y := by
            have h1 := ((hasStrictFDerivAt_id y).sub ((G.comp A).hasStrictFDerivAt)).add
              (G.hasStrictFDerivAt.comp y hf)
            have heq : Ψ = (id - ⇑(G.comp A) + fun x => G (f x)) := by funext z; simp [Ψ]
            rw [heq]
            refine h1.congr_fderiv ?_
            ext z; simp
          have hAΨ : ∀ z, A (Ψ z) = f z := by
            intro z; simp only [Ψ, map_add, map_sub, hAG]; abel
          let L := hΨ.localInverse Ψ _ y
          have hL := hΨ.to_localInverse
          refine ⟨fun s => L (Ψ y + s • d), fun s => s, ?_, ?_, rfl, hasDerivAt_id 0, ?_⟩
          · simp [L]
          · have hlin : HasDerivAt (fun s : ℝ => Ψ y + s • d) d 0 := by
              simpa using ((hasDerivAt_id (0:ℝ)).smul_const d).const_add (Ψ y)
            have hL' : HasFDerivAt L ((ContinuousLinearEquiv.refl ℝ (E n)).symm : E n →L[ℝ] E n)
                (Ψ y + (0:ℝ) • d) := by simpa using hL.hasFDerivAt
            have := hL'.comp_hasDerivAt (0:ℝ) hlin
            simp only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
              ContinuousLinearMap.id_apply] at this
            exact this
          · have hcont : Tendsto (fun s : ℝ => Ψ y + s • d) (𝓝 0) (𝓝 (Ψ y)) := by
              have : Continuous (fun s : ℝ => Ψ y + s • d) := by fun_prop
              simpa using this.tendsto 0
            filter_upwards [hcont.eventually hΨ.eventually_right_inverse] with s hs
            intro k
            have h2 := congrArg (fun v => v k) (hAΨ (L (Ψ y + s • d)))
            rw [hs] at h2
            have : f (L (Ψ y + s • d)) k = B k (L (Ψ y + s • d)) := rfl
            rw [← this, ← h2, map_add, map_smul, hAΨ]
            simp [f, hA]
        -- derivative of the Φ constraint
        have hΦd : ∀ t : ℝ, 0 < t → ∀ (i : Fin l) (y : E n),
            DifferentiableAt ℝ (fun z => PhiSU θ (P.G i z) (P.H i z) t) y ∧
            ∀ v, fderiv ℝ (fun z => PhiSU θ (P.G i z) (P.H i z) t) y v =
              fderiv ℝ (P.G i) y v + fderiv ℝ (P.H i) y v -
                deriv (fun a => phiSU θ a t) (P.G i y - P.H i y) *
                  (fderiv ℝ (P.G i) y v - fderiv ℝ (P.H i) y v) := by
          intro t ht i y
          have hd := (hϕ t ht).1 (P.G i y - P.H i y)
          have hG := ((hGC i).differentiable (by norm_num) y).hasFDerivAt
          have hH := ((hHC i).differentiable (by norm_num) y).hasFDerivAt
          have hc := (hG.add hH).sub (hd.hasDerivAt.comp_hasFDerivAt y (hG.sub hH))
          have heq : (fun z => PhiSU θ (P.G i z) (P.H i z) t) =
              (P.G i + P.H i) - (fun a => phiSU θ a t) ∘ (P.G i - P.H i) := by
            funext z; simp [PhiSU]
          rw [heq]
          refine ⟨hc.differentiableAt, fun v => ?_⟩
          rw [hc.fderiv]
          simp [smul_eq_mul]
        -- the base family
        set Q := P.TNLP xs with hQ
        let K := ↥(Q.activeSet xs) ⊕ (Fin p ⊕ ↥(P.I0p xs ∪ P.I00 xs) ⊕ ↥(P.Ip0 xs ∪ P.I00 xs))
        let B : K → E n → ℝ := Sum.elim (fun i => Q.g i.1) (fun j => Q.h j)
        have hBC : ∀ k, ContDiff ℝ 1 (B k) := by
          intro k
          rcases k with ⟨i, hi⟩ | j
          · rcases i with i | i | i
            · exact hgC i
            · exact (hHC i.1).neg
            · exact (hGC i.1).neg
          · rcases j with j | j | j
            · exact hhC j
            · exact hGC j.1
            · exact hHC j.1
        have hLIxs : LinearIndependent ℝ (fun k => gradient (B k) xs) := by
          have : (fun k => gradient (B k) xs) = Sum.elim (fun i : ↥(Q.activeSet xs) => gradient (Q.g i.1) xs)
              (fun j => gradient (Q.h j) xs) := by
            funext k; rcases k with k | k <;> rfl
          rw [this]; exact hLICQ
        have hLIev : ∀ᶠ y in 𝓝 xs, LinearIndependent ℝ (fun k => gradient (B k) y) := by
          have hcont : Continuous (fun y => fun k => gradient (B k) y) := by
            apply continuous_pi; intro k
            have : Continuous (fun y => fderiv ℝ (B k) y) := (hBC k).continuous_fderiv (by norm_num)
            exact (InnerProductSpace.toDual ℝ (E n)).symm.continuous.comp this
          exact hcont.continuousAt.preimage_mem_nhds
            ((isOpen_setOfPred_linearIndependent (𝕜 := ℝ)).mem_nhds hLIxs)
        have hS1 : ∀ᶠ y in 𝓝 xs, ∀ i, P.g i xs < 0 → P.g i y < 0 := by
          rw [eventually_all]; intro i
          by_cases h : P.g i xs < 0
          · filter_upwards [(hgC i).continuous.continuousAt.eventually_lt continuousAt_const h] with y hy
            exact fun _ => hy
          · exact Eventually.of_forall (fun y h' => absurd h' h)
        obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 < c ∧ ∀ i, (i ∈ P.I0p xs → 2 * c < P.H i xs) ∧
            (i ∈ P.Ip0 xs → 2 * c < P.G i xs) := by
          have : ∀ᶠ c in 𝓝[>] (0:ℝ), ∀ i, (i ∈ P.I0p xs → 2 * c < P.H i xs) ∧
              (i ∈ P.Ip0 xs → 2 * c < P.G i xs) := by
            rw [eventually_all]; intro i
            have h2 : Tendsto (fun c : ℝ => 2 * c) (𝓝[>] (0:ℝ)) (𝓝 0) := by
              have : Tendsto (fun c : ℝ => 2 * c) (𝓝 (0:ℝ)) (𝓝 (2 * 0)) :=
                (continuous_const.mul continuous_id).tendsto 0
              simpa using this.mono_left nhdsWithin_le_nhds
            refine Eventually.and ?_ ?_
            · by_cases hi : i ∈ P.I0p xs
              · filter_upwards [h2.eventually (gt_mem_nhds hi.2)] with c hc using fun _ => hc
              · exact Eventually.of_forall (fun c h => absurd h hi)
            · by_cases hi : i ∈ P.Ip0 xs
              · filter_upwards [h2.eventually (gt_mem_nhds hi.1)] with c hc using fun _ => hc
              · exact Eventually.of_forall (fun c h => absurd h hi)
          obtain ⟨c, hc1, hc2⟩ := (this.and self_mem_nhdsWithin).exists
          exact ⟨c, hc2, hc1⟩
        have hS2 : ∀ᶠ y in 𝓝 xs, ∀ i, (i ∈ P.I0p xs → c < P.H i y) ∧ (i ∈ P.Ip0 xs → c < P.G i y) := by
          rw [eventually_all]; intro i
          refine Eventually.and ?_ ?_
          · by_cases hi : i ∈ P.I0p xs
            · filter_upwards [continuousAt_const.eventually_lt (hHC i).continuous.continuousAt
                (show c < P.H i xs by linarith [(hc i).1 hi])] with y hy using fun _ => hy
            · exact Eventually.of_forall (fun y h => absurd h hi)
          · by_cases hi : i ∈ P.Ip0 xs
            · filter_upwards [continuousAt_const.eventually_lt (hGC i).continuous.continuousAt
                (show c < P.G i xs by linarith [(hc i).2 hi])] with y hy using fun _ => hy
            · exact Eventually.of_forall (fun y h => absurd h hi)
        set S := {y : E n | LinearIndependent ℝ (fun k => gradient (B k) y) ∧
            (∀ i, P.g i xs < 0 → P.g i y < 0) ∧
            ∀ i, (i ∈ P.I0p xs → c < P.H i y) ∧ (i ∈ P.Ip0 xs → c < P.G i y)} with hSdef
        have hSn : S ∈ 𝓝 xs := by
          filter_upwards [hLIev, hS1, hS2] with y h1 h2 h3 using ⟨h1, h2, h3⟩
        refine ⟨interior S, interior_mem_nhds.2 hSn, c, hc0, ?_⟩
        intro t ht x hxN hxF
        obtain ⟨ht0, htc⟩ := ht
        obtain ⟨hϕdiff, hϕtan, hϕm, hϕp, hϕle⟩ := hϕ t ht0
        have hxS : x ∈ S := interior_subset hxN
        -- differentiability of every constraint
        have hgD : ∀ i y, DifferentiableAt ℝ ((RSU P θ t).g i) y := by
          intro i y
          rcases i with i | i | i | i
          · exact ((hgC i).differentiable (by norm_num)) y
          · exact ((hGC i).neg.differentiable (by norm_num)) y
          · exact ((hHC i).neg.differentiable (by norm_num)) y
          · exact (hΦd t ht0 i y).1
        have hhD : ∀ j y, DifferentiableAt ℝ ((RSU P θ t).h j) y :=
          fun j y => ((hhC j).differentiable (by norm_num)) y
        have hmem : ∀ i, P.G i x = 0 → i ∈ P.I0p xs ∪ P.I00 xs := by
          intro i hi
          obtain ⟨h1, h2, h3⟩ := hxs.2.2 i
          have hG : P.G i xs = 0 := by
            by_contra hne
            have hpos : 0 < P.G i xs := lt_of_le_of_ne h1 (Ne.symm hne)
            have hH : P.H i xs = 0 := by
              rcases mul_eq_zero.1 h3 with h | h
              · exact absurd h hne
              · exact h
            have := (hxS.2.2 i).2 ⟨hpos, hH⟩
            linarith
          rcases lt_or_eq_of_le h2 with h | h
          · exact Or.inl ⟨hG, h⟩
          · exact Or.inr ⟨hG, h.symm⟩
        have hmemH : ∀ i, P.H i x = 0 → i ∈ P.Ip0 xs ∪ P.I00 xs := by
          intro i hi
          obtain ⟨h1, h2, h3⟩ := hxs.2.2 i
          have hH : P.H i xs = 0 := by
            by_contra hne
            have hpos : 0 < P.H i xs := lt_of_le_of_ne h2 (Ne.symm hne)
            have hG : P.G i xs = 0 := by
              rcases mul_eq_zero.1 h3 with h | h
              · exact h
              · exact absurd h hne
            have := (hxS.2.2 i).1 ⟨hG, hpos⟩
            linarith
          rcases lt_or_eq_of_le h1 with h | h
          · exact Or.inl ⟨h, hH⟩
          · exact Or.inr ⟨h.symm, hH⟩
        unfold IsACQ
        apply Subset.antisymm
        · intro d hd
          refine ⟨?_, ?_⟩
          · intro i hi
            rw [hgr]
            exact hT1 _ x d _ hd (hgD i x) hi (fun z hz => hz.1 i)
          · intro j
            rw [hgr]
            have h1 := hT1 _ x d _ hd (hhD j x) (hxF.2 j) (fun z hz => le_of_eq (hz.2 j))
            have h2 := hT1 _ x d (fun z => -(RSU P θ t).h j z) hd (hhD j x).neg
              (by simp [hxF.2 j]) (fun z hz => by simp [hz.2 j])
            rw [fderiv_fun_neg] at h2
            simp only [neg_apply] at h2
            linarith
        · intro d hd
          obtain ⟨hdg, hdh⟩ := hd
          simp only [hgr] at hdg hdh
          obtain ⟨φ, r, hφ0, hφd, hr0, hrd, hφB⟩ := hcurve B hBC x hxS.1 d
          apply hT2 _ x d φ hφ0 hφd
          have hφc : ContinuousAt φ 0 := hφd.continuousAt
          have hE0 : ∀ᶠ s in 𝓝 (0:ℝ), φ s ∈ S := by
            have : interior S ∈ 𝓝 (φ 0) := by rw [hφ0]; exact isOpen_interior.mem_nhds hxN
            exact Filter.mem_of_superset (hφc.preimage_mem_nhds this) (fun s (hs : s ∈ φ ⁻¹' interior S) => (interior_subset hs : φ s ∈ S))
          have hE2 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 ≤ r s := by
            have h1 := (hasDerivAt_iff_tendsto_slope.1 hrd).eventually
              (lt_mem_nhds (show (0:ℝ) < 1 by norm_num))
            have h2 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < slope r 0 s :=
              nhdsWithin_mono _ (fun x (hx : 0 < x) => ne_of_gt hx) h1
            filter_upwards [h2, self_mem_nhdsWithin] with s hs hs0
            rw [slope_def_field, hr0, sub_zero, sub_zero] at hs
            exact ((div_pos_iff_of_pos_right hs0).1 hs).le
          have hE3 : ∀ᶠ s in 𝓝 (0:ℝ), ∀ i, (RSU P θ t).g i x < 0 → (RSU P θ t).g i (φ s) < 0 := by
            rw [eventually_all]; intro i
            by_cases h : (RSU P θ t).g i x < 0
            · have hc' : ContinuousAt (fun s => (RSU P θ t).g i (φ s)) 0 :=
                (hgD i (φ 0)).continuousAt.comp hφc
              filter_upwards [hc'.eventually_lt continuousAt_const (by simpa [hφ0] using h)] with s hs
                using fun _ => hs
            · exact Eventually.of_forall (fun s h' => absurd h' h)
          filter_upwards [nhdsWithin_le_nhds hE0, nhdsWithin_le_nhds hφB, hE2, nhdsWithin_le_nhds hE3]
            with s hsS hsB hsr hsI
          refine ⟨?_, ?_⟩
          · intro i
            by_cases hin : (RSU P θ t).g i x < 0
            · exact (hsI i hin).le
            have hact : (RSU P θ t).g i x = 0 := le_antisymm (hxF.1 i) (not_lt.1 hin)
            have hdi := hdg i hact
            rcases i with i | i | i | i
            · change P.g i x = 0 at hact
              change fderiv ℝ (P.g i) x d ≤ 0 at hdi
              change P.g i (φ s) ≤ 0
              have hxa : P.g i xs = 0 := by
                by_contra hne
                have := hxS.2.1 i (lt_of_le_of_ne (hxs.1 i) hne)
                linarith
              have hb := hsB (Sum.inl ⟨Sum.inl i, hxa⟩)
              change P.g i (φ s) = P.g i x + r s * fderiv ℝ (P.g i) x d at hb
              rw [hb, hact]; nlinarith
            · change -P.G i x = 0 at hact
              change fderiv ℝ (fun z => -P.G i z) x d ≤ 0 at hdi
              rw [fderiv_fun_neg] at hdi
              simp only [neg_apply] at hdi
              change -P.G i (φ s) ≤ 0
              have hG0 : P.G i x = 0 := by linarith
              have hb := hsB (Sum.inr (Sum.inr (Sum.inl ⟨i, hmem i hG0⟩)))
              change P.G i (φ s) = P.G i x + r s * fderiv ℝ (P.G i) x d at hb
              rw [hb, hG0]; nlinarith
            · change -P.H i x = 0 at hact
              change fderiv ℝ (fun z => -P.H i z) x d ≤ 0 at hdi
              rw [fderiv_fun_neg] at hdi
              simp only [neg_apply] at hdi
              change -P.H i (φ s) ≤ 0
              have hH0 : P.H i x = 0 := by linarith
              have hb := hsB (Sum.inr (Sum.inr (Sum.inr ⟨i, hmemH i hH0⟩)))
              change P.H i (φ s) = P.H i x + r s * fderiv ℝ (P.H i) x d at hb
              rw [hb, hH0]; nlinarith
            · change PhiSU θ (P.G i x) (P.H i x) t = 0 at hact
              change fderiv ℝ (fun z => PhiSU θ (P.G i z) (P.H i z) t) x d ≤ 0 at hdi
              rw [(hΦd t ht0 i x).2 d] at hdi
              change PhiSU θ (P.G i (φ s)) (P.H i (φ s)) t ≤ 0
              unfold PhiSU at hact ⊢
              have hGx : 0 ≤ P.G i x := by have := hxF.1 (Sum.inr (Sum.inl i)); change -P.G i x ≤ 0 at this; linarith
              have hHx : 0 ≤ P.H i x := by have := hxF.1 (Sum.inr (Sum.inr (Sum.inl i))); change -P.H i x ≤ 0 at this; linarith
              have hdG : 0 ≤ fderiv ℝ (P.G i) x d ∨ P.G i x ≠ 0 := by
                by_cases h0 : P.G i x = 0
                · left
                  have := hdg (Sum.inr (Sum.inl i)) (by change -P.G i x = 0; simp [h0])
                  change fderiv ℝ (fun z => -P.G i z) x d ≤ 0 at this
                  rw [fderiv_fun_neg] at this
                  simp only [neg_apply] at this
                  linarith
                · right; exact h0
              have hdH : 0 ≤ fderiv ℝ (P.H i) x d ∨ P.H i x ≠ 0 := by
                by_cases h0 : P.H i x = 0
                · left
                  have := hdg (Sum.inr (Sum.inr (Sum.inl i))) (by change -P.H i x = 0; simp [h0])
                  change fderiv ℝ (fun z => -P.H i z) x d ≤ 0 at this
                  rw [fderiv_fun_neg] at this
                  simp only [neg_apply] at this
                  linarith
                · right; exact h0
              obtain ⟨h1, h2, h3⟩ := hxs.2.2 i
              rcases lt_or_eq_of_le h1 with hGs | hGs <;> rcases lt_or_eq_of_le h2 with hHs | hHs
              · exfalso; have := mul_pos hGs hHs; linarith
              · -- i ∈ Ip0
                have hi : i ∈ P.Ip0 xs := ⟨hGs, hHs.symm⟩
                have hGxc : c < P.G i x := (hxS.2.2 i).2 hi
                have hGyc : c < P.G i (φ s) := (hsS.2.2 i).2 hi
                have hH0 : P.H i x = 0 := by
                  by_contra hne
                  have hpos : 0 < P.H i x := lt_of_le_of_ne hHx (Ne.symm hne)
                  by_cases hcase : t ≤ |P.G i x - P.H i x|
                  · have he : phiSU θ (P.G i x - P.H i x) t = |P.G i x - P.H i x| := by simp [phiSU, hcase]
                    rw [he] at hact
                    have := abs_sub_lt_iff.2 (⟨by linarith, by linarith⟩ :
                      P.G i x - P.H i x < P.G i x + P.H i x ∧ P.H i x - P.G i x < P.G i x + P.H i x)
                    linarith
                  · have := hϕle _ (not_le.1 hcase)
                    linarith
                have hdH' := hdH.resolve_right (by simp [hH0])
                rw [hH0, hϕp _ (by linarith)] at hdi
                have hdH0 : fderiv ℝ (P.H i) x d = 0 := by linarith
                have hb := hsB (Sum.inr (Sum.inr (Sum.inr ⟨i, Or.inl hi⟩)))
                change P.H i (φ s) = P.H i x + r s * fderiv ℝ (P.H i) x d at hb
                rw [hb, hH0, hdH0]
                simp only [mul_zero, add_zero, sub_zero]
                have hcase : t ≤ |P.G i (φ s)| := by
                  rw [abs_of_pos (by linarith)]; linarith
                simp only [phiSU, if_pos hcase]
                rw [abs_of_pos (by linarith)]; linarith
              · -- i ∈ I0p
                have hi : i ∈ P.I0p xs := ⟨hGs.symm, hHs⟩
                have hHyc : c < P.H i (φ s) := (hsS.2.2 i).1 hi
                have hHxc : c < P.H i x := (hxS.2.2 i).1 hi
                have hG0 : P.G i x = 0 := by
                  by_contra hne
                  have hpos : 0 < P.G i x := lt_of_le_of_ne hGx (Ne.symm hne)
                  by_cases hcase : t ≤ |P.G i x - P.H i x|
                  · have he : phiSU θ (P.G i x - P.H i x) t = |P.G i x - P.H i x| := by simp [phiSU, hcase]
                    rw [he] at hact
                    have := abs_sub_lt_iff.2 (⟨by linarith, by linarith⟩ :
                      P.G i x - P.H i x < P.G i x + P.H i x ∧ P.H i x - P.G i x < P.G i x + P.H i x)
                    linarith
                  · have := hϕle _ (not_le.1 hcase)
                    linarith
                have hdG' := hdG.resolve_right (by simp [hG0])
                rw [hG0, hϕm _ (by linarith)] at hdi
                have hdG0 : fderiv ℝ (P.G i) x d = 0 := by linarith
                have hb := hsB (Sum.inr (Sum.inr (Sum.inl ⟨i, Or.inl hi⟩)))
                change P.G i (φ s) = P.G i x + r s * fderiv ℝ (P.G i) x d at hb
                rw [hb, hG0, hdG0]
                simp only [mul_zero, add_zero, zero_add, zero_sub]
                have hcase : t ≤ |-P.H i (φ s)| := by
                  rw [abs_neg, abs_of_pos (by linarith)]; linarith
                simp only [phiSU, if_pos hcase]
                rw [abs_neg, abs_of_pos (by linarith)]; linarith
              · -- I00
                have hi : i ∈ P.I00 xs := ⟨hGs.symm, hHs.symm⟩
                have hbG := hsB (Sum.inr (Sum.inr (Sum.inl ⟨i, Or.inr hi⟩)))
                change P.G i (φ s) = P.G i x + r s * fderiv ℝ (P.G i) x d at hbG
                have hbH := hsB (Sum.inr (Sum.inr (Sum.inr ⟨i, Or.inr hi⟩)))
                change P.H i (φ s) = P.H i x + r s * fderiv ℝ (P.H i) x d at hbH
                have htan := hϕtan (P.G i x - P.H i x) (P.G i (φ s) - P.H i (φ s))
                have key : deriv (fun a => phiSU θ a t) (P.G i x - P.H i x) *
                    (P.G i (φ s) - P.H i (φ s) - (P.G i x - P.H i x)) =
                    r s * (deriv (fun a => phiSU θ a t) (P.G i x - P.H i x) *
                      (fderiv ℝ (P.G i) x d - fderiv ℝ (P.H i) x d)) := by
                  rw [hbG, hbH]; ring
                have := mul_nonpos_of_nonneg_of_nonpos hsr hdi
                rw [hbG, hbH]
                rw [hbG, hbH] at htan key
                nlinarith
          · intro j
            have hb := hsB (Sum.inr (Sum.inl j))
            change P.h j (φ s) = P.h j x + r s * fderiv ℝ (P.h j) x d at hb
            change P.h j (φ s) = 0
            have := hdh j
            change fderiv ℝ (P.h j) x d = 0 at this
            have h0 : P.h j x = 0 := hxF.2 j
            rw [hb, this, h0]; ring
