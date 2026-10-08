-- Prove2me | solution 3 for JordanCurve.accessibility_from_arc_complement
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T16:07:26.318059+00:00
-- url     : https://prove2.me/submissions/19244465-0de5-435c-94f4-2f86289f74f4

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Bornology.Basic

theorem solution
    (hArc : ∀ α : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2),
      Continuous α → Function.Injective α →
        IsConnected ((Set.range α)ᶜ))
    (γ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      EuclideanSpace ℝ (Fin 2))
    (hγ : Continuous γ) (hinj : Function.Injective γ)
    (inside outside : Set (EuclideanSpace ℝ (Fin 2)))
    (hiopen : IsOpen inside) (hoopen : IsOpen outside)
    (hiconn : IsConnected inside) (hoconn : IsConnected outside)
    (hdisj : Disjoint inside outside)
    (hcover : inside ∪ outside = (Set.range γ)ᶜ) :
    Set.range γ ⊆ closure inside ∩ closure outside := by
  let e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr
  have hpi := Real.two_le_pi
  have hexp1 : ∀ x : ℝ, |x| < 2 * Real.pi → Complex.exp (x * Complex.I) = 1 → x = 0 := by
    intro x hx h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
    have hx' : x = n * (2 * Real.pi) := by
      have := congrArg Complex.im hn
      simpa [Complex.mul_im] using this
    have h1 : |(n:ℝ)| < 1 := by
      rw [hx', abs_mul, abs_of_pos (show (0:ℝ) < 2 * Real.pi by linarith)] at hx
      by_contra hc
      push_neg at hc
      nlinarith
    obtain ⟨h2, h3⟩ := abs_lt.mp h1
    have h4 : (-1:ℤ) < n := by exact_mod_cast h2
    have h5 : n < 1 := by exact_mod_cast h3
    have : n = 0 := by omega
    rw [hx', this]; simp
  have hec : Continuous (fun a : ℝ => Complex.exp (a * Complex.I)) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have key : ∀ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      ∀ U V : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U → IsOpen V → U.Nonempty →
        Disjoint U V → U ∪ V = (Set.range γ)ᶜ → γ z ∈ closure U := by
    intro z U V hU hV hUne hUV hUVc
    by_contra hcl
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl (γ z) hcl
    have hballU : ∀ x ∈ Metric.ball (γ z) r, x ∉ U :=
      fun x hx hxU => hball hx (subset_closure hxU)
    obtain ⟨ε, hε, hγε⟩ := Metric.continuous_iff.mp hγ z r hr
    obtain ⟨δ0, hδ0, hexpε⟩ := Metric.continuous_iff.mp hec 0 ε hε
    set δ := min δ0 1 with hδ
    have hδpos : 0 < δ := lt_min hδ0 one_pos
    have hδε : δ ≤ δ0 := min_le_left _ _
    have hδ1 : δ ≤ 1 := min_le_right _ _
    set ζ : ℂ := e.symm z with hζ
    have hζn : ‖ζ‖ = 1 := by
      rw [hζ, LinearIsometryEquiv.norm_map]
      simpa using z.2
    have hζ0 : ζ ≠ 0 := by intro h0; rw [h0] at hζn; simp at hζn
    let g : ℝ → Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := fun θ =>
      ⟨e (ζ * Complex.exp (θ * Complex.I)), by
        simp [norm_mul, hζn, Complex.norm_exp_ofReal_mul_I]⟩
    have hgc : Continuous g := by
      apply Continuous.subtype_mk
      exact e.continuous.comp (continuous_const.mul hec)
    have hginj : ∀ θ θ', |θ - θ'| < 2 * Real.pi → g θ = g θ' → θ = θ' := by
      intro θ θ' hlt h
      have h1 : ζ * Complex.exp (θ * Complex.I) = ζ * Complex.exp (θ' * Complex.I) :=
        e.injective (congrArg Subtype.val h)
      have h2 := mul_left_cancel₀ hζ0 h1
      have h3 : Complex.exp (((θ - θ' : ℝ) : ℂ) * Complex.I) = 1 := by
        rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, h2, div_self (Complex.exp_ne_zero _)]
      have := hexp1 _ hlt h3
      linarith
    set L := 2 * Real.pi - 2 * δ with hLdef
    have hL : 0 < L := by rw [hLdef]; linarith
    let α : Set.Icc (0:ℝ) 1 → EuclideanSpace ℝ (Fin 2) := fun t => γ (g (δ + t.1 * L))
    have hαc : Continuous α :=
      hγ.comp (hgc.comp (continuous_const.add (continuous_subtype_val.mul continuous_const)))
    have hαinj : Function.Injective α := by
      intro t t' h
      obtain ⟨ht0, ht1⟩ := t.2
      obtain ⟨ht0', ht1'⟩ := t'.2
      have h1 := hginj _ _ ?_ (hinj h)
      · apply Subtype.ext
        have : (t.1 - t'.1) * L = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · linarith
        · linarith
      · rw [abs_lt]; constructor <;> nlinarith
    have hg0 : g 0 = z := Subtype.ext (by simp [g, hζ])
    have hcover2 : ∀ w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
        γ w ∉ Set.range α → dist (γ w) (γ z) < r := by
      intro w hw
      apply hγε
      set u : ℂ := e.symm w with hu
      have hun : ‖u‖ = 1 := by
        rw [hu, LinearIsometryEquiv.norm_map]
        simpa using w.2
      set q := u / ζ with hqdef
      have hqn : ‖q‖ = 1 := by rw [hqdef, norm_div, hun, hζn]; norm_num
      set a := Complex.arg q with hadef
      have hq : q = Complex.exp (a * Complex.I) := by
        have := Complex.norm_mul_exp_arg_mul_I q
        rw [hqn] at this; simpa using this.symm
      have hwu : w = g a := by
        apply Subtype.ext
        show (w : EuclideanSpace ℝ (Fin 2)) = e (ζ * Complex.exp (a * Complex.I))
        rw [← hq, hqdef, mul_div_cancel₀ _ hζ0, hu]
        simp
      have ha := Complex.neg_pi_lt_arg q
      have ha' := Complex.arg_le_pi q
      by_contra hfar
      apply hw
      by_cases h1 : δ ≤ a
      · refine ⟨⟨(a - δ) / L, ?_, ?_⟩, ?_⟩
        · apply div_nonneg <;> linarith
        · rw [div_le_one hL]; linarith
        · show γ (g (δ + (a - δ) / L * L)) = γ w
          rw [hwu, div_mul_cancel₀ _ hL.ne']; congr 2; ring
      by_cases h2 : a ≤ -δ
      · refine ⟨⟨(a + 2 * Real.pi - δ) / L, ?_, ?_⟩, ?_⟩
        · apply div_nonneg <;> linarith
        · rw [div_le_one hL]; linarith
        · show γ (g (δ + (a + 2 * Real.pi - δ) / L * L)) = γ w
          rw [hwu, div_mul_cancel₀ _ hL.ne']
          congr 1
          apply Subtype.ext
          simp only [g]
          congr 2
          push_cast
          rw [show (δ:ℂ) + (a + 2 * Real.pi - δ) = a + 2 * Real.pi by ring, add_mul,
            Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
      · exfalso; apply hfar
        have habs : |a| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
        have hd := hexpε a (by simpa [Real.dist_eq] using lt_of_lt_of_le habs hδε)
        rw [hwu, ← hg0]
        rw [Subtype.dist_eq]
        simp only [g]
        rw [dist_eq_norm, ← map_sub, LinearIsometryEquiv.norm_map, ← mul_sub, norm_mul, hζn,
          one_mul, ← dist_eq_norm]
        simpa using hd
    have hS : IsClosed (Set.range α) := (isCompact_range hαc).isClosed
    have hconn := (hArc α hαc hαinj).isPreconnected
    have hSJ : Set.range α ⊆ Set.range γ := by rintro _ ⟨t, rfl⟩; exact ⟨_, rfl⟩
    have hz : γ z ∉ Set.range α := by
      rintro ⟨t, ht⟩
      obtain ⟨ht0, ht1⟩ := t.2
      have h := hinj ht
      have := hginj _ _ ?_ (h.trans hg0.symm)
      all_goals first | nlinarith | (rw [abs_lt]; constructor <;> nlinarith)
    have hsep := hconn U (V ∪ (Metric.ball (γ z) r ∩ (Set.range α)ᶜ)) hU
      (hV.union (Metric.isOpen_ball.inter hS.isOpen_compl)) ?_ ?_ ?_
    · obtain ⟨x, -, hxU, hxv⟩ := hsep
      rcases hxv with hxV | ⟨hxb, _⟩
      · exact Set.disjoint_left.mp hUV hxU hxV
      · exact hballU x hxb hxU
    · intro x hx
      by_cases hxJ : x ∈ Set.range γ
      · obtain ⟨w, rfl⟩ := hxJ
        exact Or.inr (Or.inr ⟨hcover2 w hx, hx⟩)
      · have : x ∈ U ∪ V := hUVc ▸ hxJ
        rcases this with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    · obtain ⟨x, hx⟩ := hUne
      refine ⟨x, ?_, hx⟩
      intro hxS
      have : x ∈ U ∪ V := Or.inl hx
      rw [hUVc] at this
      exact this (hSJ hxS)
    · exact ⟨γ z, hz, Or.inr ⟨Metric.mem_ball_self hr, hz⟩⟩
  rintro _ ⟨z, rfl⟩
  exact ⟨key z inside outside hiopen hoopen hiconn.nonempty hdisj hcover,
    key z outside inside hoopen hiopen hoconn.nonempty hdisj.symm
      (by rw [Set.union_comm]; exact hcover)⟩
