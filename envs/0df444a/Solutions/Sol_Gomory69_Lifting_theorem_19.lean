-- Prove2me | solution 1 for Gomory69.Lifting.theorem_19
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:28:13.835653+00:00
-- url     : https://prove2.me/submissions/b8d08240-a5bf-4e95-8eb2-d64376c4bb45

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



/-- linear map sending a vector on `Plus H` to its placement on cell `φ h + k`. -/
def ellK (ψ : G →+ H) (φ : H → G) (k : G) : (Plus H → ℝ) →ₗ[ℝ] (Plus G → ℝ) :=
  LinearMap.pi fun g : Plus G =>
    if hg : ψ (g : G) = 0 then 0
    else if (g : G) = φ (ψ (g : G)) + k then
      (LinearMap.proj (⟨ψ (g : G), hg⟩ : Plus H) : (Plus H → ℝ) →ₗ[ℝ] ℝ)
    else 0

theorem ellK_apply (ψ : G →+ H) (φ : H → G) (k : G) (x : Plus H → ℝ) (g : Plus G) :
    ellK ψ φ k x g =
      if hg : ψ (g : G) = 0 then 0
      else if (g : G) = φ (ψ (g : G)) + k then x ⟨ψ (g : G), hg⟩ else 0 := by
  unfold ellK
  simp only [LinearMap.pi_apply]
  by_cases hg : ψ (g : G) = 0
  · simp [hg]
  · by_cases h2 : (g : G) = φ (ψ (g : G)) + k
    · simp only [dif_neg hg, if_pos h2]; rfl
    · simp only [dif_neg hg, if_neg h2]; rfl

theorem castVec_base (ψ : G →+ H) (φ : H → G) (k : G) (τ : Plus H → ℕ) :
    castVec (liftedPathBase ψ φ k τ) = ellK ψ φ k (castVec τ) := by
  funext g
  rw [ellK_apply]
  unfold castVec liftedPathBase
  by_cases hg : ψ (g : G) = 0
  · simp [hg]
  · by_cases h2 : (g : G) = φ (ψ (g : G)) + k
    · simp only [dif_neg hg, if_pos h2]
    · simp only [dif_neg hg, if_neg h2]; simp

theorem rank_D_core (ψ : G →+ H) (hψ : Function.Surjective ψ) (g₀ : G) (hg₀ : ψ g₀ ≠ 0)
    (π' : Plus H → ℝ) (π₀ : ℝ) (hπ₀ : 0 < π₀) (hface : IsFace H (ψ g₀) π' π₀) :
    ∃ s : Fin (Fintype.card (Plus G)) → (Plus G → ℕ),
      (∀ i, s i ∈ T G g₀ ∧ liftCoeff ψ π' ⬝ᵥ castVec (s i) = π₀) ∧
        LinearIndependent ℝ (fun i => castVec (s i)) := by
  haveI : Nontrivial H := ⟨⟨ψ g₀, 0, hg₀⟩⟩
  obtain ⟨-, sH, hsH, hliH⟩ := (face_iff_core (ψ g₀) π' π₀ hπ₀).mp hface
  have hspanH : Submodule.span ℝ (Set.range (fun i => castVec (sH i))) = ⊤ := by
    apply hliH.span_eq_top_of_card_eq_finrank'
    simp
  obtain ⟨g1, hg1⟩ := exists_ne (0 : H)
  have hcardH : 0 < Fintype.card (Plus H) := Fintype.card_pos_iff.mpr ⟨⟨g1, hg1⟩⟩
  let i0 : Fin (Fintype.card (Plus H)) := ⟨0, hcardH⟩
  let φ : H → G := Function.surjInv hψ
  have hφ : ∀ h, ψ (φ h) = h := Function.surjInv_eq hψ
  let A : Set (Plus G → ℕ) := {t | t ∈ T G g₀ ∧ liftCoeff ψ π' ⬝ᵥ castVec t = π₀}
  let SG := Submodule.span ℝ (castVec '' A)
  have hA : ∀ t ∈ A, castVec t ∈ SG := fun t ht => Submodule.subset_span ⟨t, ht, rfl⟩
  -- base tight point
  have hlp := fun (k : G) (hk : ψ k = 0) (i : Fin (Fintype.card (Plus H))) =>
    liftedPath_minimal_core ψ φ hφ g₀ π' π₀ (sH i) (hsH i).1 (hsH i).2 k hk
  -- step 1: kernel unit vectors
  have hker : ∀ κ : Plus G, ψ (κ : G) = 0 → (Pi.single κ (1:ℝ) : Plus G → ℝ) ∈ SG := by
    intro κ hκ
    obtain ⟨hc, hT, hval⟩ := hlp 0 (map_zero ψ) i0
    set t0 := liftedPath ψ φ g₀ 0 (sH i0) with ht0
    set n := addOrderOf (κ : G) with hn
    have hnpos : 0 < n := addOrderOf_pos _
    set t1 : Plus G → ℕ := t0 + n • Pi.single κ 1 with ht1
    have hsum1 : ∑ g : Plus G, t1 g • (g : G) = g₀ := by
      have e : ∀ g : Plus G, t1 g • (g : G) = t0 g • (g : G) + (n • (Pi.single κ 1 : Plus G → ℕ) g) • (g : G) := by
        intro g; simp [ht1, add_smul]
      simp only [e, Finset.sum_add_distrib]
      rw [hT.1]
      have : ∑ g : Plus G, (n • (Pi.single κ 1 : Plus G → ℕ) g) • (g : G) = 0 := by
        rw [Finset.sum_eq_single κ]
        · simp [hn]
        · intro b _ hb; simp [Pi.single_eq_of_ne hb]
        · simp
      rw [this, add_zero]
    have hA1 : t1 ∈ A := by
      refine ⟨⟨hsum1, ?_⟩, ?_⟩
      · intro h0
        have := congrFun h0 κ
        simp [ht1] at this
        omega
      · have : liftCoeff ψ π' ⬝ᵥ castVec t1 =
            liftCoeff ψ π' ⬝ᵥ castVec t0 + n * liftCoeff ψ π' κ := by
          have hc1 : castVec t1 = castVec t0 + (n : ℝ) • Pi.single κ 1 := by
            funext g
            by_cases hg : g = κ
            · subst hg; simp [castVec, ht1]
            · simp [castVec, ht1, Pi.single_eq_of_ne hg]
          rw [hc1, dotProduct_add, dotProduct_smul]
          simp [dotProduct_single]
        rw [this, hval]
        have : liftCoeff ψ π' κ = 0 := by simp [liftCoeff, hκ, ext]
        rw [this]; simp
    have h1 := hA t1 hA1
    have h0 : castVec t0 ∈ SG := hA t0 ⟨hT, hval⟩
    have hdiff : (n : ℝ) • (Pi.single κ (1:ℝ) : Plus G → ℝ) ∈ SG := by
      have : (n : ℝ) • (Pi.single κ (1:ℝ) : Plus G → ℝ) = castVec t1 - castVec t0 := by
        funext g
        by_cases hg : g = κ
        · subst hg; simp [castVec, ht1]
        · simp [castVec, ht1, Pi.single_eq_of_ne hg]
      rw [this]; exact Submodule.sub_mem _ h1 h0
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
    have := Submodule.smul_mem SG ((n : ℝ)⁻¹) hdiff
    rwa [smul_smul, inv_mul_cancel₀ hn0, one_smul] at this
  -- step 2
  have hell : ∀ k : G, ψ k = 0 → ∀ x : Plus H → ℝ, ellK ψ φ k x ∈ SG := by
    intro k hk x
    have hle : Submodule.span ℝ (Set.range (fun i => castVec (sH i))) ≤
        Submodule.comap (ellK ψ φ k) SG := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap]
      obtain ⟨hc, hT, hval⟩ := hlp k hk i
      have hmem := hA _ ⟨hT, hval⟩
      rw [← castVec_base ψ φ k (sH i)]
      have : castVec (liftedPathBase ψ φ k (sH i)) =
          castVec (liftedPath ψ φ g₀ k (sH i)) -
            (fun g : Plus G => if (g : G) = closingElement ψ φ g₀ k (sH i) then (1:ℝ) else 0) := by
        funext g
        simp only [castVec, liftedPath, Pi.sub_apply]
        push_cast
        ring
      rw [this]
      refine Submodule.sub_mem _ hmem ?_
      by_cases h0 : closingElement ψ φ g₀ k (sH i) = 0
      · have : (fun g : Plus G => if (g : G) = closingElement ψ φ g₀ k (sH i) then (1:ℝ) else 0) = 0 := by
          funext g; simp [h0, g.2]
        rw [this]; exact Submodule.zero_mem _
      · have : (fun g : Plus G => if (g : G) = closingElement ψ φ g₀ k (sH i) then (1:ℝ) else 0) =
            Pi.single (⟨_, h0⟩ : Plus G) 1 := by
          funext g
          by_cases hg : g = ⟨_, h0⟩
          · subst hg; simp
          · have : (g : G) ≠ closingElement ψ φ g₀ k (sH i) := fun h => hg (Subtype.ext h)
            simp [this, Pi.single_eq_of_ne hg]
        rw [this]
        exact hker _ hc
    have : x ∈ Submodule.comap (ellK ψ φ k) SG := by
      apply hle; rw [hspanH]; trivial
    exact this
  -- step 3
  have hall : ∀ g : Plus G, (Pi.single g (1:ℝ) : Plus G → ℝ) ∈ SG := by
    intro g
    by_cases hg : ψ (g : G) = 0
    · exact hker g hg
    · set h : Plus H := ⟨ψ (g : G), hg⟩ with hh
      have hk : ψ ((g : G) - φ h) = 0 := by rw [map_sub, hφ]; simp [hh]
      have := hell _ hk (Pi.single h 1)
      have e : ellK ψ φ ((g : G) - φ h) (Pi.single h 1) = Pi.single g 1 := by
        funext g'
        rw [ellK_apply]
        by_cases hg' : ψ (g' : G) = 0
        · have : g' ≠ g := fun e => hg (e ▸ hg')
          simp [hg', Pi.single_eq_of_ne this]
        · rw [dif_neg hg']
          by_cases h2 : (g' : G) = φ (ψ (g' : G)) + ((g : G) - φ h)
          · rw [if_pos h2]
            by_cases h3 : (⟨ψ (g' : G), hg'⟩ : Plus H) = h
            · have h4 : ψ (g' : G) = ψ (g : G) := congrArg Subtype.val h3
              have : g' = g := by
                apply Subtype.ext
                rw [h2, h4]
                have : φ (ψ (g : G)) = φ h := rfl
                rw [this]; abel
              subst this; simp [h3]
            · have : g' ≠ g := by
                intro e; apply h3; subst e; rfl
              rw [Pi.single_eq_of_ne h3, Pi.single_eq_of_ne this]
          · rw [if_neg h2]
            have : g' ≠ g := by
              intro e; apply h2; subst e
              have : φ (ψ (g' : G)) = φ h := rfl
              rw [this]; abel
            rw [Pi.single_eq_of_ne this]
      rw [e] at this
      exact this
  have hSG : SG = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun ℝ (Plus G)).span_eq, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    simpa using hall g
  obtain ⟨s, hs1, hs2⟩ := span_to_indep A hSG
  exact ⟨s, fun i => hs1 i, hs2⟩



theorem theorem_19_core (ψ : G →+ H) (hψ : Function.Surjective ψ) (g₀ : G) (hg₀ : ψ g₀ ≠ 0)
    (π' : Plus H → ℝ) (π₀ : ℝ) (hπ₀ : 0 < π₀) (hface : IsFace H (ψ g₀) π' π₀) :
    IsFace G g₀ (liftCoeff ψ π') π₀ := by
  haveI : Nontrivial G := ⟨⟨g₀, 0, fun h => hg₀ (by rw [h, map_zero])⟩⟩
  have hv := hface.2.1
  have hvalid := (pushForward_path_core ψ g₀ hg₀ π' π₀).2 hv
  obtain ⟨s, hs, hli⟩ := rank_D_core ψ hψ g₀ hg₀ π' π₀ hπ₀ hface
  exact face_core_bwd _ π₀ hπ₀ g₀ hvalid s hs hli

end A
end Gomory69.Lifting

open Gomory69.Lifting


theorem solution {G H : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup H] [Fintype H] [DecidableEq H]
    (ψ : G →+ H) (hψ : Function.Surjective ψ) (g₀ : G) (hg₀ : ψ g₀ ≠ 0)
    (π' : Plus H → ℝ) (π₀ : ℝ) (hπ₀ : 0 < π₀) (hface : IsFace H (ψ g₀) π' π₀) :
    IsFace G g₀ (liftCoeff ψ π') π₀ := by
  exact theorem_19_core ψ hψ g₀ hg₀ π' π₀ hπ₀ hface
