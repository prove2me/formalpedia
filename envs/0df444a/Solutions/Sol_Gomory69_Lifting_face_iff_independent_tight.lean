-- Prove2me | solution 1 for Gomory69.Lifting.face_iff_independent_tight
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:24:59.226715+00:00
-- url     : https://prove2.me/submissions/e3763474-1017-482e-a6a7-91f98354a8aa

import Mathlib
import Definitions.Def_Gomory69_Lifting_GroupPolyhedron
import Definitions.Def_Gomory69_Lifting_Lift



namespace Gomory69.Lifting

theorem span_to_indep {G : Type*} [Fintype G] (A : Set (G → ℕ)) 
    (h : Submodule.span ℝ (Set.image (fun t : G → ℕ => fun g => (t g : ℝ)) A) = ⊤) :
    ∃ s : Fin (Fintype.card G) → (G → ℕ), (∀ i, s i ∈ A) ∧
      LinearIndependent ℝ (fun i => fun g => ((s i) g : ℝ)) := by
  classical
  let v : A → (G → ℝ) := fun t g => ((t.1 g : ℕ) : ℝ)
  have hr : Set.range v = Set.image (fun t : G → ℕ => fun g => (t g : ℝ)) A := by
    ext x; simp [v]
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' ℝ v
  have : Finite κ := hli.finite
  have : Fintype κ := Fintype.ofFinite κ
  have hsp' : Submodule.span ℝ (Set.range (v ∘ a)) = ⊤ := by rw [hsp, hr, h]
  have hcard : Fintype.card κ = Fintype.card G := by
    have := finrank_span_eq_card hli
    rw [hsp'] at this
    simp at this
    omega
  let e : Fin (Fintype.card G) ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => (a (e i)).1, fun i => (a (e i)).2, ?_⟩
  exact hli.comp e e.injective

section A
variable {G H : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem sumPush {M : Type*} [AddCommMonoid M] (ψ : G →+ H) (u : H → M) (hu : u 0 = 0)
    (w : Plus G → ℕ) :
    ∑ g : Plus G, w g • u (ψ (g : G)) = ∑ h : Plus H, pushForward ψ w h • u (h : H) := by
  have h1 : ∀ h : Plus H, pushForward ψ w h • u (h : H) =
      ∑ g : Plus G, if ψ (g : G) = (h : H) then w g • u (ψ (g : G)) else 0 := by
    intro h
    unfold pushForward
    rw [Finset.sum_smul, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro g _
    by_cases hg : ψ (g : G) = (h : H)
    · simp [hg]
    · simp [hg]
  simp_rw [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : ψ (g : G) = 0
  · simp [hg, hu]
  · rw [Finset.sum_eq_single ⟨ψ (g : G), hg⟩]
    · simp
    · intro b _ hb
      have : ψ (g : G) ≠ (b : H) := fun h => hb (Subtype.ext h.symm)
      simp [this]
    · simp

theorem pushForward_mem (ψ : G →+ H) (g₀ : G) (hg₀ : ψ g₀ ≠ 0) (t : Plus G → ℕ)
    (ht : t ∈ T G g₀) : pushForward ψ t ∈ T H (ψ g₀) := by
  obtain ⟨h1, h2⟩ := ht
  constructor
  · have := sumPush ψ (fun h : H => h) rfl t
    rw [← this, ← h1]
    simp [map_sum, map_nsmul]
  · intro h0
    apply hg₀
    have : ∑ h : Plus H, pushForward ψ t h • (h : H) = 0 := by simp [h0]
    rw [← this, ← sumPush ψ (fun h : H => h) rfl t, ← h1]
    simp [map_sum, map_nsmul]

theorem lift_dot (ψ : G →+ H) (π' : Plus H → ℝ) (t : Plus G → ℕ) :
    liftCoeff ψ π' ⬝ᵥ castVec t = π' ⬝ᵥ castVec (pushForward ψ t) := by
  have := sumPush ψ (ext π') (by simp [ext]) t
  simp only [dotProduct, liftCoeff, castVec]
  have e1 : ∀ g : Plus G, ext π' (ψ (g:G)) * (t g : ℝ) = t g • ext π' (ψ (g:G)) := by
    intro g; rw [nsmul_eq_mul, mul_comm]
  have e2 : ∀ h : Plus H, π' h * (pushForward ψ t h : ℝ) = pushForward ψ t h • ext π' (h:H) := by
    intro h; rw [nsmul_eq_mul, mul_comm]; simp [ext, h.2]
  simp_rw [e1, e2]
  exact this

theorem pushForward_path_core (ψ : G →+ H) (g₀ : G) (hg₀ : ψ g₀ ≠ 0) (π' : Plus H → ℝ) (π₀ : ℝ) :
    (∀ t ∈ T G g₀, pushForward ψ t ∈ T H (ψ g₀) ∧
        liftCoeff ψ π' ⬝ᵥ castVec t = π' ⬝ᵥ castVec (pushForward ψ t)) ∧
      ((∀ τ ∈ T H (ψ g₀), π₀ ≤ π' ⬝ᵥ castVec τ) →
        ∀ t ∈ T G g₀, π₀ ≤ liftCoeff ψ π' ⬝ᵥ castVec t) := by
  refine ⟨fun t ht => ⟨pushForward_mem ψ g₀ hg₀ t ht, lift_dot ψ π' t⟩, fun h t ht => ?_⟩
  rw [lift_dot]
  exact h _ (pushForward_mem ψ g₀ hg₀ t ht)



theorem base_push (ψ : G →+ H) (φ : H → G) (hφ : ∀ h, ψ (φ h) = h) (k : G) (hk : ψ k = 0)
    (τ : Plus H → ℕ) : pushForward ψ (liftedPathBase ψ φ k τ) = τ := by
  funext h
  have hne : ψ (φ h + k) = (h : H) := by rw [map_add, hφ, hk, add_zero]
  have hne0 : φ (h:H) + k ≠ 0 := fun h0 => h.2 (by rw [← hne, h0, map_zero])
  unfold pushForward
  rw [Finset.sum_eq_single (⟨φ h + k, hne0⟩ : Plus G)]
  · have hh : ψ (φ (h:H) + k) ≠ 0 := by rw [hne]; exact h.2
    simp only [liftedPathBase]
    rw [dif_neg hh, if_pos (by simp [hne])]
    congr 1
    exact Subtype.ext hne
  · intro g hg hgne
    have hg' : ψ (g:G) = (h:H) := (Finset.mem_filter.mp hg).2
    have hh : ψ (g:G) ≠ 0 := by rw [hg']; exact h.2
    simp only [liftedPathBase]
    rw [dif_neg hh, if_neg]
    intro hc
    apply hgne
    apply Subtype.ext
    rw [hc, hg']
  · intro h'
    exfalso; apply h'
    simp [hne]

theorem liftedPath_minimal_core (ψ : G →+ H) (φ : H → G) (hφ : ∀ h, ψ (φ h) = h) (g₀ : G)
    (π' : Plus H → ℝ) (π₀ : ℝ) (τ : Plus H → ℕ) (hτ : τ ∈ T H (ψ g₀))
    (hτπ : π' ⬝ᵥ castVec τ = π₀) (k : G) (hk : ψ k = 0) :
    ψ (closingElement ψ φ g₀ k τ) = 0 ∧
      liftedPath ψ φ g₀ k τ ∈ T G g₀ ∧
        liftCoeff ψ π' ⬝ᵥ castVec (liftedPath ψ φ g₀ k τ) = π₀ := by
  have hB : ψ (∑ g : Plus G, liftedPathBase ψ φ k τ g • (g : G)) = ψ g₀ := by
    have := sumPush ψ (fun h : H => h) rfl (liftedPathBase ψ φ k τ)
    rw [base_push ψ φ hφ k hk τ] at this
    rw [map_sum]
    simpa [map_nsmul, hτ.1] using this.trans hτ.1
  have hc : ψ (closingElement ψ φ g₀ k τ) = 0 := by
    unfold closingElement
    rw [map_sub, hB, sub_self]
  have hsum : ∑ g : Plus G, (if (g : G) = closingElement ψ φ g₀ k τ then 1 else 0 : ℕ) • (g : G)
      = closingElement ψ φ g₀ k τ := by
    by_cases h0 : closingElement ψ φ g₀ k τ = 0
    · simp only [h0]
      exact Finset.sum_eq_zero (fun x _ => by simp [x.2])
    · rw [Finset.sum_eq_single (⟨_, h0⟩ : Plus G)]
      · simp
      · intro g _ hg
        have : (g : G) ≠ closingElement ψ φ g₀ k τ := fun h => hg (Subtype.ext h)
        simp [this]
      · simp
  have hpush : pushForward ψ (liftedPath ψ φ g₀ k τ) = τ := by
    funext h
    have : pushForward ψ (liftedPath ψ φ g₀ k τ) h =
        pushForward ψ (liftedPathBase ψ φ k τ) h := by
      unfold pushForward
      apply Finset.sum_congr rfl
      intro g hg
      have hg' : ψ (g:G) = (h:H) := (Finset.mem_filter.mp hg).2
      have : (g : G) ≠ closingElement ψ φ g₀ k τ := by
        intro e
        apply h.2
        rw [← hg', e, hc]
      simp [liftedPath, this]
    rw [this, base_push ψ φ hφ k hk τ]
  refine ⟨hc, ⟨?_, ?_⟩, ?_⟩
  · simp only [liftedPath, add_smul, Finset.sum_add_distrib, hsum]
    unfold closingElement; abel
  · intro h0
    obtain ⟨h, hh⟩ : ∃ h, τ h ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hτ.2 (funext hcon)
    have h1 : liftedPath ψ φ g₀ k τ = 0 := h0
    have := congrFun hpush h
    rw [h1] at this
    simp [pushForward] at this
    exact hh this.symm
  · rw [lift_dot, hpush, hτπ]



theorem face_core_fwd (π : Plus G → ℝ) (π₀ : ℝ) (hπ₀ : 0 < π₀) (g₀ : G)
    (hf : IsFace G g₀ π π₀) :
    Submodule.span ℝ (castVec '' {t | t ∈ T G g₀ ∧ π ⬝ᵥ castVec t = π₀}) = ⊤ := by
  obtain ⟨hne, hvalid, haff⟩ := hf
  set P := castVec '' {t | t ∈ T G g₀ ∧ π ⬝ᵥ castVec t = π₀} with hP
  have hsub : ∀ x : Plus G → ℝ, π ⬝ᵥ x = π₀ → x ∈ Submodule.span ℝ P := by
    intro x hx
    have : x ∈ (affineSpan ℝ P : Set (Plus G → ℝ)) := by
      rw [haff]; exact hx
    have h2 := affineSpan_le_toAffineSubspace_span (k := ℝ) (s := P) this
    exact h2
  obtain ⟨i, hi⟩ : ∃ i, π i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (funext hcon)
  set p : Plus G → ℝ := (π₀ / π i) • Pi.single i 1 with hp
  have hpπ : π ⬝ᵥ p = π₀ := by
    rw [hp, dotProduct_smul]
    simp [dotProduct_single]
    field_simp
  rw [eq_top_iff]
  intro x _
  set r := π ⬝ᵥ x
  set w := x - (r / π₀) • p with hw
  have hwπ : π ⬝ᵥ w = 0 := by
    rw [hw, dotProduct_sub, dotProduct_smul, hpπ]
    simp only [smul_eq_mul]
    field_simp
    ring
  have h1 : w + p ∈ Submodule.span ℝ P := hsub _ (by rw [dotProduct_add, hwπ, hpπ, zero_add])
  have h2 : p ∈ Submodule.span ℝ P := hsub _ hpπ
  have : x = (w + p) - p + (r / π₀) • p := by rw [hw]; abel
  rw [this]
  exact Submodule.add_mem _ (Submodule.sub_mem _ h1 h2) (Submodule.smul_mem _ _ h2)



theorem face_core_bwd [Nontrivial G] (π : Plus G → ℝ) (π₀ : ℝ) (hπ₀ : 0 < π₀) (g₀ : G)
    (hvalid : ∀ t ∈ T G g₀, π₀ ≤ π ⬝ᵥ castVec t)
    (s : Fin (Fintype.card (Plus G)) → (Plus G → ℕ))
    (hs : ∀ i, s i ∈ T G g₀ ∧ π ⬝ᵥ castVec (s i) = π₀)
    (hli : LinearIndependent ℝ (fun i => castVec (s i))) : IsFace G g₀ π π₀ := by
  obtain ⟨g1, hg1⟩ := exists_ne (0 : G)
  have hcard : 0 < Fintype.card (Plus G) := Fintype.card_pos_iff.mpr ⟨⟨g1, hg1⟩⟩
  let i0 : Fin (Fintype.card (Plus G)) := ⟨0, hcard⟩
  refine ⟨?_, hvalid, ?_⟩
  · intro h0
    have := (hs i0).2
    rw [h0] at this
    simp at this
    linarith
  · have hspan : Submodule.span ℝ (Set.range (fun i => castVec (s i))) = ⊤ := by
      apply hli.span_eq_top_of_card_eq_finrank'
      simp
    let HP : AffineSubspace ℝ (Plus G → ℝ) :=
      { carrier := {x | π ⬝ᵥ x = π₀}
        smul_vsub_vadd_mem' := by
          intro c p1 p2 p3 h1 h2 h3
          simp only [Set.mem_setOf_eq, vsub_eq_sub, vadd_eq_add] at *
          rw [dotProduct_add, dotProduct_smul, dotProduct_sub, h1, h2, h3]
          simp }
    have hmem : ∀ i, castVec (s i) ∈ (HP : Set (Plus G → ℝ)) := fun i => (hs i).2
    ext x
    constructor
    · intro hx
      have : affineSpan ℝ (castVec '' {t | t ∈ T G g₀ ∧ π ⬝ᵥ castVec t = π₀}) ≤ HP := by
        rw [affineSpan_le]
        rintro _ ⟨t, ht, rfl⟩
        exact ht.2
      exact this hx
    · intro hx
      have hx' : π ⬝ᵥ x = π₀ := hx
      have hxs : x ∈ Submodule.span ℝ (Set.range (fun i => castVec (s i))) := by
        rw [hspan]; trivial
      rw [Submodule.mem_span_range_iff_exists_fun] at hxs
      obtain ⟨c, hc⟩ := hxs
      have hsumc : ∑ i, c i = 1 := by
        have : π ⬝ᵥ x = ∑ i, c i * π₀ := by
          rw [← hc, dotProduct_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [dotProduct_smul, (hs i).2]; rfl
        rw [hx', ← Finset.sum_mul] at this
        have : (∑ i, c i) * π₀ = 1 * π₀ := by linarith
        exact mul_right_cancel₀ hπ₀.ne' this
      set Q := castVec '' {t | t ∈ T G g₀ ∧ π ⬝ᵥ castVec t = π₀} with hQ
      have hQi : ∀ i, castVec (s i) ∈ Q := fun i => ⟨s i, hs i, rfl⟩
      have hdir : x - castVec (s i0) ∈ (affineSpan ℝ Q).direction := by
        rw [direction_affineSpan]
        have : x - castVec (s i0) = ∑ i, c i • (castVec (s i) - castVec (s i0)) := by
          simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsumc, one_smul]
          rw [hc]
        rw [this]
        refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ ?_)
        exact vsub_mem_vectorSpan ℝ (hQi i) (hQi i0)
      have := AffineSubspace.vadd_mem_of_mem_direction hdir (mem_affineSpan ℝ (hQi i0))
      simpa using this

theorem face_iff_core [Nontrivial G] (g₀ : G) (π : Plus G → ℝ) (π₀ : ℝ) (hπ₀ : 0 < π₀) :
    IsFace G g₀ π π₀ ↔
      (∀ t ∈ T G g₀, π₀ ≤ π ⬝ᵥ castVec t) ∧
        ∃ s : Fin (Fintype.card (Plus G)) → (Plus G → ℕ),
          (∀ i, s i ∈ T G g₀ ∧ π ⬝ᵥ castVec (s i) = π₀) ∧
            LinearIndependent ℝ (fun i => castVec (s i)) := by
  constructor
  · intro hf
    refine ⟨hf.2.1, ?_⟩
    have := face_core_fwd π π₀ hπ₀ g₀ hf
    obtain ⟨s, hs1, hs2⟩ := span_to_indep {t | t ∈ T G g₀ ∧ π ⬝ᵥ castVec t = π₀} this
    exact ⟨s, hs1, hs2⟩
  · rintro ⟨hv, s, hs, hli⟩
    exact face_core_bwd π π₀ hπ₀ g₀ hv s hs hli

end A
end Gomory69.Lifting

open Gomory69.Lifting


theorem solution {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [Nontrivial G]
    (g₀ : G) (π : Plus G → ℝ) (π₀ : ℝ) (hπ₀ : 0 < π₀) :
    IsFace G g₀ π π₀ ↔
      (∀ t ∈ T G g₀, π₀ ≤ π ⬝ᵥ castVec t) ∧
        ∃ s : Fin (Fintype.card (Plus G)) → (Plus G → ℕ),
          (∀ i, s i ∈ T G g₀ ∧ π ⬝ᵥ castVec (s i) = π₀) ∧
            LinearIndependent ℝ (fun i => castVec (s i)) := by
  exact face_iff_core g₀ π π₀ hπ₀
