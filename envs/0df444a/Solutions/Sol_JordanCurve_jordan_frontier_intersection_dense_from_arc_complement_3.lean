-- Prove2me | solution 3 for JordanCurve.jordan_frontier_intersection_dense_from_arc_complement
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T16:22:27.618997+00:00
-- url     : https://prove2.me/submissions/3aed2986-359e-4939-a6cb-aa8df92c3ee1

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
    Set.range γ ⊆ closure (frontier inside ∩ frontier outside) := by
  rintro _ ⟨z, rfl⟩
  have hn : ∀ v : EuclideanSpace ℝ (Fin 2), ‖v‖ = 1 ↔ v 0 ^ 2 + v 1 ^ 2 = 1 := by
    intro v; rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]; simp
  have hz : z.1 0 ^ 2 + z.1 1 ^ 2 = 1 := (hn z.1).1 (by simpa using z.2)
  set z0 := z.1 0
  set z1 := z.1 1
  let W : ℝ → EuclideanSpace ℝ (Fin 2) := fun θ =>
    !₂[z0 * Real.cos θ - z1 * Real.sin θ, z0 * Real.sin θ + z1 * Real.cos θ]
  have hW : ∀ θ, W θ ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro θ
    rw [mem_sphere_zero_iff_norm, hn]
    simp only [W]
    simp
    nlinarith [Real.sin_sq_add_cos_sq θ]
  let ws : ℝ → Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := fun θ => ⟨W θ, hW θ⟩
  have hwsc : Continuous ws := by
    apply Continuous.subtype_mk
    simp only [W]
    fun_prop
  have hws0 : ws 0 = z := by
    apply Subtype.ext
    ext i; fin_cases i <;> simp [ws, W, z0, z1]
  have hwsinj : ∀ θ θ', ws θ = ws θ' → -(2 * Real.pi) < θ - θ' → θ - θ' < 2 * Real.pi →
      θ = θ' := by
    intro θ θ' h h1 h2
    have e0 := congrArg (fun u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 => u.1 0) h
    have e1 := congrArg (fun u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 => u.1 1) h
    simp [ws, W] at e0 e1
    have hc : Real.cos θ = Real.cos θ' := by linear_combination z0 * e0 + z1 * e1 - (Real.cos θ - Real.cos θ') * hz
    have hs : Real.sin θ = Real.sin θ' := by linear_combination z0 * e1 - z1 * e0 - (Real.sin θ - Real.sin θ') * hz
    have : Real.cos (θ - θ') = 1 := by
      rw [Real.cos_sub, hc, hs]; nlinarith [Real.sin_sq_add_cos_sq θ']
    linarith [(Real.cos_eq_one_iff_of_lt_of_lt h1 h2).1 this]
  have hsurj : ∀ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      ∃ θ, -Real.pi < θ ∧ θ ≤ Real.pi ∧ u = ws θ := by
    intro u
    have hu : u.1 0 ^ 2 + u.1 1 ^ 2 = 1 := (hn u.1).1 (by simpa using u.2)
    set ζ : ℂ := ⟨u.1 0 * z0 + u.1 1 * z1, u.1 1 * z0 - u.1 0 * z1⟩
    have hζ2 : ‖ζ‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_mk]
      nlinarith
    have hζ : ‖ζ‖ = 1 := by
      have := norm_nonneg ζ
      nlinarith
    have hζ0 : ζ ≠ 0 := by intro h; rw [h] at hζ; simp at hζ
    refine ⟨Complex.arg ζ, Complex.neg_pi_lt_arg ζ, Complex.arg_le_pi ζ, ?_⟩
    have hc : Real.cos (Complex.arg ζ) = u.1 0 * z0 + u.1 1 * z1 := by
      rw [Complex.cos_arg hζ0, hζ, div_one]
    have hs : Real.sin (Complex.arg ζ) = u.1 1 * z0 - u.1 0 * z1 := by
      rw [Complex.sin_arg, hζ, div_one]
    apply Subtype.ext
    ext i; fin_cases i <;> simp [ws, W]
    · linear_combination -(u.1 0) * hz - z0 * hc + z1 * hs
    · linear_combination -(u.1 1) * hz - z0 * hs - z1 * hc
  have key : ∀ A B : Set (EuclideanSpace ℝ (Fin 2)), IsOpen A → IsOpen B →
      A.Nonempty → B.Nonempty → Disjoint A B → A ∪ B = (Set.range γ)ᶜ →
      γ z ∈ closure A := by
    intro A B hA hB hAne hBne hAB hABc
    rw [Metric.mem_closure_iff]
    intro ε hε
    by_contra hcon
    push_neg at hcon
    have hfc : Continuous (fun θ => γ (ws θ)) := hγ.comp hwsc
    obtain ⟨a0, ha0, hball⟩ := Metric.continuous_iff.1 hfc 0 ε hε
    set a := min a0 1 with ha
    have hapos : 0 < a := lt_min ha0 one_pos
    have ha1 : a ≤ 1 := min_le_right _ _
    have haa0 : a ≤ a0 := min_le_left _ _
    have hpi := Real.two_le_pi
    let α : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2) :=
      fun t => γ (ws (a + t.1 * (2 * Real.pi - 2 * a)))
    have hαc : Continuous α := hfc.comp (by fun_prop)
    have hαi : Function.Injective α := by
      intro t t' h
      have h' := hwsinj _ _ (hinj h)
      have := t.2; have := t'.2
      apply Subtype.ext
      have hpos : 0 < 2 * Real.pi - 2 * a := by linarith
      have e : a + t.1 * (2 * Real.pi - 2 * a) = a + t'.1 * (2 * Real.pi - 2 * a) := by
        apply h' <;> nlinarith [this, t.2.1, t.2.2, t'.2.1, t'.2.2]
      have := mul_right_cancel₀ hpos.ne' (by linarith : t.1 * (2 * Real.pi - 2 * a) = t'.1 * (2 * Real.pi - 2 * a))
      exact this
    have hS := (hArc α hαc hαi).isPreconnected
    have hαsub : Set.range α ⊆ Set.range γ := by
      rintro _ ⟨t, rfl⟩; exact ⟨_, rfl⟩
    have hAS : A ⊆ (Set.range α)ᶜ := fun x hx hx' =>
      (hABc ▸ Set.subset_union_left : A ⊆ (Set.range γ)ᶜ) hx (hαsub hx')
    have hBS : B ⊆ (Set.range α)ᶜ := fun x hx hx' =>
      (hABc ▸ Set.subset_union_right : B ⊆ (Set.range γ)ᶜ) hx (hαsub hx')
    obtain ⟨x, hxS, hxA, hxB⟩ := hS A (B ∪ Metric.ball (γ z) ε) hA
      (hB.union Metric.isOpen_ball) (by
        intro x hx
        by_cases hxr : x ∈ Set.range γ
        · obtain ⟨u, rfl⟩ := hxr
          obtain ⟨θ, h1, h2, rfl⟩ := hsurj u
          by_cases hθ : |θ| < a
          · right; right
            have := hball θ (by simpa [Real.dist_eq] using lt_of_lt_of_le hθ haa0)
            rw [hws0] at this
            rw [Metric.mem_ball]; exact this
          · exfalso; apply hx
            have hpos : 0 < 2 * Real.pi - 2 * a := by linarith
            rcases le_or_gt 0 θ with h0 | h0
            · rw [abs_of_nonneg h0] at hθ
              refine ⟨⟨(θ - a) / (2 * Real.pi - 2 * a), ?_, ?_⟩, ?_⟩
              · apply div_nonneg <;> linarith
              · rw [div_le_one hpos]; linarith
              · simp only [α]
                have : a + (θ - a) / (2 * Real.pi - 2 * a) *
                    (2 * Real.pi - 2 * a) = θ := by
                  rw [div_mul_cancel₀ _ hpos.ne']; ring
                rw [this]
            · rw [abs_of_neg h0] at hθ
              refine ⟨⟨(θ + 2 * Real.pi - a) / (2 * Real.pi - 2 * a), ?_, ?_⟩, ?_⟩
              · apply div_nonneg <;> linarith
              · rw [div_le_one hpos]; linarith
              · simp only [α]
                have : a + (θ + 2 * Real.pi - a) / (2 * Real.pi - 2 * a) *
                    (2 * Real.pi - 2 * a) = θ + 2 * Real.pi := by
                  rw [div_mul_cancel₀ _ hpos.ne']; ring
                rw [this]
                congr 1
                apply Subtype.ext
                simp [ws, W]
        · have : x ∈ A ∪ B := hABc ▸ hxr
          rcases this with h | h
          · left; exact h
          · right; left; exact h)
      (by obtain ⟨x, hx⟩ := hAne; exact ⟨x, hAS hx, hx⟩)
      (by obtain ⟨x, hx⟩ := hBne; exact ⟨x, hBS hx, Or.inl hx⟩)
    rcases hxB with h | h
    · exact Set.disjoint_left.1 hAB hxA h
    · have := hcon x hxA
      rw [Metric.mem_ball, dist_comm] at h
      linarith
  have hnot : ∀ C : Set (EuclideanSpace ℝ (Fin 2)), C ⊆ (Set.range γ)ᶜ → γ z ∉ C :=
    fun C hC h => hC h ⟨z, rfl⟩
  have h1 := key inside outside hiopen hoopen hiconn.nonempty hoconn.nonempty hdisj hcover
  have h2 := key outside inside hoopen hiopen hoconn.nonempty hiconn.nonempty hdisj.symm
    (by rw [Set.union_comm]; exact hcover)
  apply subset_closure
  constructor
  · rw [frontier, hiopen.interior_eq]
    exact ⟨h1, hnot _ (hcover ▸ Set.subset_union_left)⟩
  · rw [frontier, hoopen.interior_eq]
    exact ⟨h2, hnot _ (hcover ▸ Set.subset_union_right)⟩
