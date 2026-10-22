-- Prove2me | solution 1 for ModernConvex.CQRepr.convex_hull_union_cqr
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T15:56:52.304389+00:00
-- url     : https://prove2.me/submissions/d6f44665-c44e-403e-b444-978639a45c2a

import Mathlib
import Definitions.Def_ModernConvex_CQRepr_CQR

open Matrix

open ModernConvex.CQRepr

open Pointwise

theorem g70mc2_vec {κ : Type*} [Fintype κ] [DecidableEq κ] (g : (κ → ℝ) →ₗ[ℝ] ℝ) :
    ∀ z : κ → ℝ, g z = (fun j => g (Pi.single j 1)) ⬝ᵥ z := by
  intro z
  conv_lhs => rw [show z = ∑ j, z j • Pi.single j (1:ℝ) by
    ext k; simp [Finset.sum_apply, Pi.single_apply]]
  simp [map_sum, dotProduct, mul_comm]

theorem g70mc2_cqr_of_blocks {n : ℕ} {J U : Type} [Fintype J] [DecidableEq J] [Fintype U]
    [DecidableEq U] (d : J → ℕ) (hd : ∀ j, 1 ≤ d j)
    (L : (j : J) → ((Fin n → ℝ) × (U → ℝ)) →ₗ[ℝ] (Fin (d j + 1) → ℝ))
    (c : (j : J) → Fin (d j + 1) → ℝ) (S : Set (Fin n → ℝ))
    (hS : ∀ x, x ∈ S ↔ ∃ u : U → ℝ, ∀ j, Real.sqrt (∑ i : Fin (d j),
      (L j (x, u) + c j) (Fin.castSucc i) ^ 2) ≤ (L j (x, u) + c j) (Fin.last _)) :
    IsCQr S := by
  set eJ := Fintype.equivFin J
  set eU := Fintype.equivFin U
  let K : IceCreamProduct := ⟨Fintype.card J, fun j' => d (eJ.symm j'), fun j' => hd _⟩
  let A : Matrix K.Idx (Fin n) ℝ := fun r a => L (eJ.symm r.1) (Pi.single a 1, 0) r.2
  let B : Matrix K.Idx (Fin (Fintype.card U)) ℝ := fun r c' =>
    L (eJ.symm r.1) (0, Pi.single (eU.symm c') 1) r.2
  let bb : K.Idx → ℝ := fun r => c (eJ.symm r.1) r.2
  have key : ∀ (x : Fin n → ℝ) (u : U → ℝ) (r : K.Idx),
      (A *ᵥ x + B *ᵥ (u ∘ eU.symm) + bb) r = (L (eJ.symm r.1) (x, u) + c (eJ.symm r.1)) r.2 := by
    intro x u r
    set j := eJ.symm r.1
    have h1 : (A *ᵥ x) r = L j (x, 0) r.2 := by
      have := g70mc2_vec ((LinearMap.proj r.2).comp ((L j).comp (LinearMap.inl ℝ _ _))) x
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
        Function.eval, LinearMap.inl_apply] at this
      rw [this]; rfl
    have h2 : (B *ᵥ (u ∘ eU.symm)) r = L j (0, u) r.2 := by
      have := g70mc2_vec ((LinearMap.proj r.2).comp ((L j).comp (LinearMap.inr ℝ _ _))) u
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
        Function.eval, LinearMap.inr_apply] at this
      rw [this]
      simp only [mulVec, dotProduct, Function.comp_apply, B]
      exact Fintype.sum_equiv eU.symm _ _ (fun c' => rfl)
    have h3 : L j (x, u) = L j (x, 0) + L j (0, u) := by
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
    show (A *ᵥ x) r + (B *ᵥ (u ∘ eU.symm)) r + c j r.2 = (L j (x, u) + c j) r.2
    rw [h1, h2, h3]; simp only [Pi.add_apply]
  refine ⟨K, Fintype.card U, A, B, bb, ?_⟩
  ext x
  rw [hS]
  simp only [cqrSet, Set.mem_setOf_eq, IceCreamProduct.cone]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u ∘ eU.symm, fun j' => ?_⟩
    simp only [key]
    exact hu (eJ.symm j')
  · rintro ⟨u', hu'⟩
    refine ⟨u' ∘ eU, ?_⟩
    have e : u' = (u' ∘ eU) ∘ eU.symm := by ext; simp
    rw [e] at hu'
    refine (eJ.symm.surjective.forall (p := fun j => Real.sqrt (∑ i : Fin (d j),
      (L j (x, u' ∘ eU) + c j) (Fin.castSucc i) ^ 2) ≤ (L j (x, u' ∘ eU) + c j) (Fin.last _))).mpr
      fun j' => ?_
    have := hu' j'
    simp only [key] at this
    exact this

abbrev g70mc2_J {k : ℕ} (K : Fin k → IceCreamProduct) (n : ℕ) : Type :=
  (Σ i, Fin (K i).N) ⊕ (Fin k ⊕ (Fin n ⊕ Unit))

abbrev g70mc2_U {k : ℕ} (n : ℕ) (p : Fin k → ℕ) : Type :=
  (Fin k × Fin n) ⊕ (Fin k ⊕ (Σ i, Fin (p i)))

def g70mc2_d {k : ℕ} (K : Fin k → IceCreamProduct) (n : ℕ) : g70mc2_J K n → ℕ
  | .inl q => (K q.1).d q.2
  | .inr _ => 1

theorem g70mc2_d_pos {k : ℕ} (K : Fin k → IceCreamProduct) (n : ℕ) (j : g70mc2_J K n) :
    1 ≤ g70mc2_d K n j := by
  rcases j with q | _
  · exact (K q.1).two_le q.2
  · exact le_rfl

noncomputable def g70mc2_L {n k : ℕ} (K : Fin k → IceCreamProduct) (p : Fin k → ℕ)
    (A : (i : Fin k) → Matrix (K i).Idx (Fin n) ℝ) (B : (i : Fin k) → Matrix (K i).Idx (Fin (p i)) ℝ)
    (b : (i : Fin k) → (K i).Idx → ℝ) :
    (j : g70mc2_J K n) → ((Fin n → ℝ) × (g70mc2_U n p → ℝ)) →ₗ[ℝ] (Fin (g70mc2_d K n j + 1) → ℝ)
  | .inl ⟨i, j'⟩ =>
    { toFun := fun xu r => (A i *ᵥ (fun a => xu.2 (.inl (i, a))) +
        B i *ᵥ (fun c => xu.2 (.inr (.inr ⟨i, c⟩))) + xu.2 (.inr (.inl i)) • b i) ⟨j', r⟩
      map_add' := fun u v => by
        ext r
        simp only [Prod.snd_add, Pi.add_apply, mulVec, dotProduct, add_mul, mul_add,
          Finset.sum_add_distrib, smul_eq_mul, Pi.smul_apply]
        ring
      map_smul' := fun c u => by
        ext r
        simp only [Prod.smul_snd, Pi.smul_apply, mulVec, dotProduct, smul_eq_mul, Pi.add_apply,
          RingHom.id_apply, Finset.mul_sum]
        ring_nf
        simp only [Finset.mul_sum]
        ring_nf }
  | .inr (.inl i) =>
    { toFun := fun xu r => if (r : ℕ) = 0 then 0 else xu.2 (.inr (.inl i))
      map_add' := fun u v => by
        funext r
        erw [Pi.add_apply]
        split_ifs <;> simp
      map_smul' := fun c u => by
        funext r
        erw [Pi.smul_apply]
        split_ifs <;> simp }
  | .inr (.inr (.inl a)) =>
    { toFun := fun xu r => if (r : ℕ) = 0 then xu.1 a - ∑ i, xu.2 (.inl (i, a)) else 0
      map_add' := fun u v => by
        funext r
        erw [Pi.add_apply]
        split_ifs <;> simp [Finset.sum_add_distrib]; ring
      map_smul' := fun c u => by
        funext r
        erw [Pi.smul_apply]
        split_ifs
        · simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_sub,
            Finset.mul_sum, RingHom.id_apply]
        · simp }
  | .inr (.inr (.inr _)) =>
    { toFun := fun xu r => if (r : ℕ) = 0 then ∑ i, xu.2 (.inr (.inl i)) else 0
      map_add' := fun u v => by
        funext r
        erw [Pi.add_apply]
        split_ifs <;> simp [Finset.sum_add_distrib]
      map_smul' := fun c u => by
        funext r
        erw [Pi.smul_apply]
        split_ifs <;> simp [Finset.mul_sum] }

def g70mc2_c {n k : ℕ} (K : Fin k → IceCreamProduct) :
    (j : g70mc2_J K n) → Fin (g70mc2_d K n j + 1) → ℝ
  | .inl _ => 0
  | .inr (.inl _) => 0
  | .inr (.inr (.inl _)) => 0
  | .inr (.inr (.inr _)) => fun r => if (r : ℕ) = 0 then -1 else 0

theorem g70mc2_condK {n k : ℕ} (K : Fin k → IceCreamProduct) (p : Fin k → ℕ)
    (A : (i : Fin k) → Matrix (K i).Idx (Fin n) ℝ) (B : (i : Fin k) → Matrix (K i).Idx (Fin (p i)) ℝ)
    (b : (i : Fin k) → (K i).Idx → ℝ) (x : Fin n → ℝ) (u : g70mc2_U n p → ℝ) (i : Fin k)
    (j' : Fin (K i).N) :
    (Real.sqrt (∑ r : Fin (g70mc2_d K n (.inl ⟨i, j'⟩)),
      (g70mc2_L K p A B b (.inl ⟨i, j'⟩) (x, u) + g70mc2_c (n := n) K (.inl ⟨i, j'⟩)) (Fin.castSucc r) ^ 2) ≤
      (g70mc2_L K p A B b (.inl ⟨i, j'⟩) (x, u) + g70mc2_c (n := n) K (.inl ⟨i, j'⟩)) (Fin.last _)) ↔
    (Real.sqrt (∑ r : Fin ((K i).d j'), (A i *ᵥ (fun a => u (.inl (i, a))) +
        B i *ᵥ (fun c => u (.inr (.inr ⟨i, c⟩))) + u (.inr (.inl i)) • b i) ⟨j', Fin.castSucc r⟩ ^ 2)
      ≤ (A i *ᵥ (fun a => u (.inl (i, a))) +
        B i *ᵥ (fun c => u (.inr (.inr ⟨i, c⟩))) + u (.inr (.inl i)) • b i) ⟨j', Fin.last _⟩) := by
  change (Real.sqrt (∑ r : Fin ((K i).d j'), ((A i *ᵥ (fun a => u (.inl (i, a))) +
        B i *ᵥ (fun c => u (.inr (.inr ⟨i, c⟩))) + u (.inr (.inl i)) • b i) ⟨j', Fin.castSucc r⟩
        + 0) ^ 2) ≤ (A i *ᵥ (fun a => u (.inl (i, a))) +
        B i *ᵥ (fun c => u (.inr (.inr ⟨i, c⟩))) + u (.inr (.inl i)) • b i) ⟨j', Fin.last _⟩ + 0) ↔ _
  simp only [add_zero]

theorem g70mc2_cond2 (α β : ℝ) (g : Fin 2 → ℝ) :
    (Real.sqrt (∑ r : Fin 1, ((if ((Fin.castSucc r : Fin 2) : ℕ) = 0 then α else β) +
      g (Fin.castSucc r)) ^ 2) ≤
      (if ((Fin.last 1 : Fin 2) : ℕ) = 0 then α else β) + g (Fin.last 1)) ↔
      |α + g 0| ≤ β + g 1 := by
  simp [Real.sqrt_sq_eq_abs]
theorem g70mc2_cone_smul (K : IceCreamProduct) (c : ℝ) (hc : 0 ≤ c) (y : K.Idx → ℝ)
    (hy : y ∈ K.cone) : c • y ∈ K.cone := by
  intro j
  have := hy j
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  exact mul_le_mul_of_nonneg_left this hc

theorem g70mc2_cone_add (K : IceCreamProduct) (y z : K.Idx → ℝ)
    (hy : y ∈ K.cone) (hz : z ∈ K.cone) : y + z ∈ K.cone := by
  intro j
  have h1 := hy j
  have h2 := hz j
  let Y : EuclideanSpace ℝ (Fin (K.d j)) := WithLp.toLp 2 fun i => y ⟨j, Fin.castSucc i⟩
  let Z : EuclideanSpace ℝ (Fin (K.d j)) := WithLp.toLp 2 fun i => z ⟨j, Fin.castSucc i⟩
  have hY : ‖Y‖ = Real.sqrt (∑ i : Fin (K.d j), y ⟨j, Fin.castSucc i⟩ ^ 2) := by
    rw [EuclideanSpace.norm_eq]; simp [Y]
  have hZ : ‖Z‖ = Real.sqrt (∑ i : Fin (K.d j), z ⟨j, Fin.castSucc i⟩ ^ 2) := by
    rw [EuclideanSpace.norm_eq]; simp [Z]
  have hYZ : ‖Y + Z‖ = Real.sqrt (∑ i : Fin (K.d j), (y + z) ⟨j, Fin.castSucc i⟩ ^ 2) := by
    rw [EuclideanSpace.norm_eq]; simp [Y, Z]
  have := norm_add_le Y Z
  have hYZ' : Real.sqrt (∑ i : Fin (K.d j), (y + z) ⟨j, Fin.castSucc i⟩ ^ 2) ≤
      (y + z) ⟨j, Fin.last (K.d j)⟩ := by
    rw [← hYZ, Pi.add_apply]; linarith
  exact hYZ'


theorem g70mc2_zero_mem (K : IceCreamProduct) : (0 : K.Idx → ℝ) ∈ K.cone := fun j => by simp

theorem g70mc2_scale_mem {n p : ℕ} (K : IceCreamProduct) (A : Matrix K.Idx (Fin n) ℝ)
    (B : Matrix K.Idx (Fin p) ℝ) (b : K.Idx → ℝ) (ξ : Fin n → ℝ) (η : Fin p → ℝ) (t : ℝ)
    (ht : 0 < t) (h : A *ᵥ ξ + B *ᵥ η + t • b ∈ K.cone) : t⁻¹ • ξ ∈ cqrSet K A B b := by
  refine ⟨t⁻¹ • η, ?_⟩
  have := g70mc2_cone_smul K t⁻¹ (inv_nonneg.mpr ht.le) _ h
  convert this using 1
  simp only [mulVec_smul, smul_add, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]

theorem g70mc2_rec_mem {n p : ℕ} (K : IceCreamProduct) (A : Matrix K.Idx (Fin n) ℝ)
    (B : Matrix K.Idx (Fin p) ℝ) (b : K.Idx → ℝ) (ξ : Fin n → ℝ) (η : Fin p → ℝ)
    (h : A *ᵥ ξ + B *ᵥ η ∈ K.cone) : ξ ∈ recessiveCone (cqrSet K A B b) := by
  rintro x ⟨u, hu⟩ s hs
  refine ⟨u + s • η, ?_⟩
  have := g70mc2_cone_add K _ _ hu (g70mc2_cone_smul K s hs _ h)
  convert this using 1
  simp only [mulVec_add, mulVec_smul, smul_add]; abel

theorem g70mc2_rec_bounded {n : ℕ} (S : Set (Fin n → ℝ)) (hS : Bornology.IsBounded S)
    (hne : S.Nonempty) (h : Fin n → ℝ) (hh : h ∈ recessiveCone S) : h = 0 := by
  by_contra hne0
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨R, hR⟩ := hS.exists_norm_le
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr hne0
  set s : ℝ := (R + ‖x0‖ + 1) / ‖h‖
  have hs : 0 ≤ s := by
    have := (norm_nonneg x0).trans (hR x0 hx0)
    positivity
  have h1 := hR _ (hh x0 hx0 s hs)
  have h2 : ‖s • h‖ ≤ ‖x0 + s • h‖ + ‖x0‖ := by
    calc ‖s • h‖ = ‖(x0 + s • h) - x0‖ := by simp
      _ ≤ _ := norm_sub_le _ _
  rw [norm_smul, Real.norm_of_nonneg hs, div_mul_cancel₀ _ hn.ne'] at h2
  linarith

theorem g70mc2_rec_add {n : ℕ} (W : Set (Fin n → ℝ)) (h1 h2 : Fin n → ℝ)
    (hh1 : h1 ∈ recessiveCone W) (hh2 : h2 ∈ recessiveCone W) : h1 + h2 ∈ recessiveCone W := by
  intro w hw s hs
  have := hh2 _ (hh1 w hw s hs) s hs
  rwa [add_assoc, ← smul_add] at this

theorem g70mc2_rec_sum {n k : ℕ} (W : Set (Fin n → ℝ)) (f : Fin k → Fin n → ℝ)
    (hf : ∀ i, f i ∈ recessiveCone W) : ∑ i, f i ∈ recessiveCone W := by
  refine Finset.sum_induction f (· ∈ recessiveCone W) (fun a b ha hb => g70mc2_rec_add W a b ha hb)
    ?_ fun i _ => hf i
  intro w hw s _; simpa using hw

theorem g70mc2_rec_ZW {n : ℕ} (Z W : Set (Fin n → ℝ)) (hZ : Bornology.IsBounded Z)
    (hZne : Z.Nonempty) (hWc : Convex ℝ W) (hWcl : IsClosed W) (h : Fin n → ℝ)
    (hh : h ∈ recessiveCone (Z + W)) : h ∈ recessiveCone W := by
  intro w hw s hs
  obtain ⟨z0, hz0⟩ := hZne
  obtain ⟨R, hR⟩ := hZ.exists_norm_le
  have hmem : ∀ j : ℕ, ∃ z ∈ Z, ∃ w' ∈ W, z + w' = z0 + w + (s * ((j : ℝ) + 1)) • h := by
    intro j
    obtain ⟨z, hz, w', hw', e⟩ := hh (z0 + w) (Set.add_mem_add hz0 hw) (s * ((j : ℝ) + 1)) (by positivity)
    exact ⟨z, hz, w', hw', e⟩
  choose z hz w' hw' e using hmem
  set θ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hθ : ∀ j, 0 < θ j ∧ θ j ≤ 1 := by
    intro j; constructor
    · positivity
    · simp only [θ]; rw [div_le_one (by positivity)]; linarith [(j.cast_nonneg : (0:ℝ) ≤ j)]
  have hp : ∀ j, (1 - θ j) • w + θ j • w' j ∈ W := fun j =>
    hWc hw (hw' j) (by linarith [(hθ j).2]) (hθ j).1.le (by ring)
  have hpe : ∀ j, (1 - θ j) • w + θ j • w' j = (w + s • h) + θ j • (z0 - z j) := by
    intro j
    have hw'e : w' j = z0 + w + (s * ((j : ℝ) + 1)) • h - z j := by rw [← e j]; abel
    rw [hw'e]
    have : θ j * (s * ((j : ℝ) + 1)) = s := by simp only [θ]; field_simp
    simp only [smul_sub, smul_add, smul_smul, this, sub_smul, one_smul]
    abel
  have hlim : Filter.Tendsto (fun j => (w + s • h) + θ j • (z0 - z j)) Filter.atTop
      (nhds (w + s • h)) := by
    conv => rhs; rw [← add_zero (w + s • h)]
    apply tendsto_const_nhds.add
    apply squeeze_zero_norm (a := fun j => θ j * (2 * R))
    · intro j
      rw [norm_smul, Real.norm_of_nonneg (hθ j).1.le]
      apply mul_le_mul_of_nonneg_left _ (hθ j).1.le
      calc ‖z0 - z j‖ ≤ ‖z0‖ + ‖z j‖ := norm_sub_le _ _
        _ ≤ 2 * R := by linarith [hR z0 hz0, hR _ (hz j)]
    · have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (2 * R)
      simpa [θ] using this
  exact hWcl.mem_of_tendsto hlim (Filter.Eventually.of_forall fun j => hpe j ▸ hp j)

theorem g70mc2_cc_mem {n k : ℕ} (X : Fin k → Set (Fin n → ℝ)) (t : Fin k → ℝ)
    (y : Fin k → Fin n → ℝ) (hy : ∀ i, y i ∈ X i) (ht : ∀ i, 0 ≤ t i) (hs : ∑ i, t i = 1) :
    ∑ i, t i • y i ∈ convexHull ℝ (⋃ i, X i) :=
  (convex_convexHull ℝ _).sum_mem (fun i _ => ht i) hs
    (fun i _ => subset_convexHull ℝ _ (Set.mem_iUnion.mpr ⟨i, hy i⟩))

theorem solution {n k : ℕ} (K : Fin k → IceCreamProduct) (p : Fin k → ℕ)
    (A : (i : Fin k) → Matrix (K i).Idx (Fin n) ℝ) (B : (i : Fin k) → Matrix (K i).Idx (Fin (p i)) ℝ)
    (b : (i : Fin k) → (K i).Idx → ℝ) (X : Fin k → Set (Fin n → ℝ))
    (hX : ∀ i, X i = cqrSet (K i) (A i) (B i) (b i))
    (hne : ∀ i, (X i).Nonempty) (hconv : ∀ i, Convex ℝ (X i)) :
    let Y : Set (Fin n → ℝ) :=
      {x | ∃ (ξ : Fin k → Fin n → ℝ) (t : Fin k → ℝ) (η : (i : Fin k) → Fin (p i) → ℝ),
        (∀ i, A i *ᵥ ξ i + B i *ᵥ η i + t i • b i ∈ (K i).cone) ∧
        (∀ i, 0 ≤ t i) ∧ ∑ i, ξ i = x ∧ ∑ i, t i = 1}
    (convexHull ℝ (⋃ i, X i) ⊆ Y ∧ Y ⊆ closure (convexHull ℝ (⋃ i, X i))) ∧
      (((∀ i, IsClosed (X i) ∧ Bornology.IsBounded (X i)) ∨
          (∃ (Z : Fin k → Set (Fin n → ℝ)) (W : Set (Fin n → ℝ)),
            (∀ i, IsClosed (Z i) ∧ Bornology.IsBounded (Z i)) ∧ Convex ℝ W ∧ IsClosed W ∧
              ∀ i, X i = Z i + W)) →
        convexHull ℝ (⋃ i, X i) = Y ∧ Y = closure (convexHull ℝ (⋃ i, X i)) ∧
          IsCQr (convexHull ℝ (⋃ i, X i))) := by
  intro Y
  set C := convexHull ℝ (⋃ i, X i) with hC
  choose x0 hx0 using hne
  have hu0 : ∀ i, ∃ u, A i *ᵥ x0 i + B i *ᵥ u + b i ∈ (K i).cone := by
    intro i; have := hx0 i; rw [hX i] at this; exact this
  choose u0 hu0 using hu0
  -- (a)
  have hYconv : Convex ℝ Y := by
    rintro x ⟨ξ, t, η, h1, h2, h3, h4⟩ x' ⟨ξ', t', η', h1', h2', h3', h4'⟩ a a' ha ha' haa
    refine ⟨fun i => a • ξ i + a' • ξ' i, fun i => a * t i + a' * t' i,
      fun i => a • η i + a' • η' i, fun i => ?_, fun i => by have := h2 i; have := h2' i; positivity,
      ?_, ?_⟩
    · have := g70mc2_cone_add _ _ _ (g70mc2_cone_smul _ a ha _ (h1 i))
        (g70mc2_cone_smul _ a' ha' _ (h1' i))
      convert this using 1
      simp only [mulVec_add, mulVec_smul, smul_add, add_smul, smul_smul]; abel
    · rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, h3, h3']
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h4, h4']; linarith
  have hXY : ∀ i, X i ⊆ Y := by
    intro i x hx
    rw [hX i] at hx
    obtain ⟨u, hu⟩ := hx
    refine ⟨Pi.single i x, Pi.single i 1, Pi.single i u, fun j => ?_, fun j => ?_, ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj; simpa using hu
      · simp [hj, g70mc2_zero_mem]
    · by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    · simp
    · simp
  have hCY : C ⊆ Y := convexHull_min (Set.iUnion_subset hXY) hYconv
  -- (b)
  have hYcl : Y ⊆ closure C := by
    rintro x ⟨ξ, t, η, h1, h2, h3, h4⟩
    have hk : (k : ℝ) ≠ 0 := by
      rintro hk0
      have : k = 0 := by exact_mod_cast hk0
      subst this; simp at h4
    have hkpos : (0 : ℝ) < k := lt_of_le_of_ne (Nat.cast_nonneg k) (Ne.symm hk)
    set m : ℝ := (k : ℝ)⁻¹
    have hm : 0 < m := inv_pos.mpr hkpos
    set ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 2)
    have hε : ∀ j, 0 < ε j ∧ ε j < 1 := by
      intro j; constructor
      · positivity
      · simp only [ε]; rw [div_lt_one (by positivity)]; linarith [(j.cast_nonneg : (0:ℝ) ≤ j)]
    have hpt : ∀ j, (1 - ε j) • x + (ε j * m) • ∑ i, x0 i ∈ C := by
      intro j
      obtain ⟨e0, e1⟩ := hε j
      set t' : Fin k → ℝ := fun i => (1 - ε j) * t i + ε j * m
      have ht' : ∀ i, 0 < t' i := fun i => by
        have := h2 i; have : 0 < 1 - ε j := by linarith
        positivity
      set ξ' : Fin k → Fin n → ℝ := fun i => (1 - ε j) • ξ i + (ε j * m) • x0 i
      have hmem : ∀ i, (t' i)⁻¹ • ξ' i ∈ X i := by
        intro i
        rw [hX i]
        apply g70mc2_scale_mem _ _ _ _ _ ((1 - ε j) • η i + (ε j * m) • u0 i) _ (ht' i)
        have := g70mc2_cone_add _ _ _ (g70mc2_cone_smul _ (1 - ε j) (by linarith) _ (h1 i))
          (g70mc2_cone_smul _ (ε j * m) (by positivity) _ (hu0 i))
        convert this using 1
        simp only [t', ξ', mulVec_add, mulVec_smul, smul_add, add_smul, smul_smul]; abel
      have hsum : ∑ i, t' i = 1 := by
        simp only [t', Finset.sum_add_distrib, ← Finset.mul_sum, h4, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show (k : ℝ) * m = 1 by simp only [m]; field_simp]
        ring
      have := g70mc2_cc_mem X t' _ hmem (fun i => (ht' i).le) hsum
      convert this using 1
      simp only [smul_smul, fun i => mul_inv_cancel₀ (ht' i).ne', one_smul, ξ',
        Finset.sum_add_distrib, ← Finset.smul_sum, h3]
    have hlim : Filter.Tendsto (fun j => (1 - ε j) • x + (ε j * m) • ∑ i, x0 i) Filter.atTop
        (nhds x) := by
      have hε0 : Filter.Tendsto ε Filter.atTop (nhds 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
          (Filter.tendsto_add_atTop_nat 1)
        refine this.congr fun j => ?_
        simp only [Function.comp_apply, ε]; push_cast; ring_nf
      have h1 := ((tendsto_const_nhds (x := (1:ℝ))).sub hε0).smul_const x
      have h2 := (hε0.mul_const m).smul_const (∑ i, x0 i)
      have := h1.add h2
      simpa using this
    exact mem_closure_of_tendsto hlim (Filter.Eventually.of_forall hpt)
  refine ⟨⟨hCY, hYcl⟩, fun H => ?_⟩
  -- representation
  have hrep : ∀ x ∈ Y, ∃ t : Fin k → ℝ, ∃ y : Fin k → Fin n → ℝ, (∀ i, 0 ≤ t i) ∧
      ∑ i, t i = 1 ∧ (∀ i, y i ∈ X i) ∧ x = ∑ i, t i • y i := by
    rintro x ⟨ξ, t, η, h1, h2, h3, h4⟩
    have hrec : ∀ i, t i = 0 → ξ i ∈ recessiveCone (X i) := by
      intro i hti
      rw [hX i]
      apply g70mc2_rec_mem _ _ _ _ _ (η i)
      simpa [hti] using h1 i
    have hpos : ∀ i, t i ≠ 0 → (t i)⁻¹ • ξ i ∈ X i := by
      intro i hti
      rw [hX i]
      exact g70mc2_scale_mem _ _ _ _ _ _ _ (lt_of_le_of_ne (h2 i) (Ne.symm hti)) (h1 i)
    rcases H with H | ⟨Z, W, hZ, hWc, hWcl, hXZ⟩
    · have hz : ∀ i, t i = 0 → ξ i = 0 := fun i hti =>
        g70mc2_rec_bounded _ (H i).2 ⟨x0 i, hx0 i⟩ _ (hrec i hti)
      refine ⟨t, fun i => if t i = 0 then x0 i else (t i)⁻¹ • ξ i, h2, h4, fun i => ?_, ?_⟩
      · by_cases hti : t i = 0
        · simp [hti, hx0 i]
        · simp [hti, hpos i hti]
      · rw [← h3]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hti : t i = 0
        · simp [hti, hz i hti]
        · simp [hti, smul_smul, mul_inv_cancel₀ hti]
    · obtain ⟨j0, hj0⟩ : ∃ j0, t j0 ≠ 0 := by
        by_contra hc; push Not at hc
        simp [hc] at h4
      have hZne : ∀ i, (Z i).Nonempty := by
        intro i
        obtain ⟨z, hz, w, hw, -⟩ := (hXZ i) ▸ hx0 i
        exact ⟨z, hz⟩
      have hrecW : ∀ i, t i = 0 → ξ i ∈ recessiveCone W := by
        intro i hti
        have := hrec i hti
        rw [hXZ i] at this
        exact g70mc2_rec_ZW _ _ (hZ i).2 (hZne i) hWc hWcl _ this
      set h : Fin n → ℝ := ∑ i, if t i = 0 then ξ i else 0
      have hh : h ∈ recessiveCone W := by
        apply g70mc2_rec_sum
        intro i
        by_cases hti : t i = 0
        · simp [hti, hrecW i hti]
        · simp only [hti, if_false]
          intro w hw s _; simpa using hw
      refine ⟨t, fun i => if t i = 0 then x0 i else if i = j0 then (t j0)⁻¹ • (ξ j0 + h)
        else (t i)⁻¹ • ξ i, h2, h4, fun i => ?_, ?_⟩
      · by_cases hti : t i = 0
        · simp [hti, hx0 i]
        · simp only [hti, if_false]
          by_cases hij : i = j0
          · subst hij
            have := hpos i hti
            rw [hXZ i] at this ⊢
            obtain ⟨z, hz, w, hw, e⟩ := this
            refine ⟨z, hz, w + (t i)⁻¹ • h, hh w hw _ (inv_nonneg.mpr (h2 i)), ?_⟩
            simp only [if_true]
            rw [smul_add, ← e]; simp only [add_assoc]
          · simp [hij, hpos i hti]
      · have e1 : ∀ i, t i • (if t i = 0 then x0 i else if i = j0 then (t j0)⁻¹ • (ξ j0 + h)
            else (t i)⁻¹ • ξ i) = (if t i = 0 then 0 else ξ i) + (if i = j0 then h else 0) := by
          intro i
          by_cases hti : t i = 0
          · have hij : i ≠ j0 := fun e => hj0 (e ▸ hti)
            simp [hti, hij]
          · by_cases hij : i = j0
            · subst hij; simp [hti, smul_smul, mul_inv_cancel₀ hti, smul_add]
            · simp [hti, hij, smul_smul, mul_inv_cancel₀ hti]
        rw [Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_add_distrib, Finset.sum_ite_eq',
          if_pos (Finset.mem_univ _), ← h3, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hti : t i = 0 <;> simp [hti]
  have hYC : Y ⊆ C := by
    intro x hx
    obtain ⟨t, y, ht, hs, hy, rfl⟩ := hrep x hx
    exact g70mc2_cc_mem X t y hy ht hs
  have hCeq : C = Y := le_antisymm hCY hYC
  -- closedness
  set f : (Fin k → ℝ) × (Fin k → Fin n → ℝ) → (Fin n → ℝ) := fun q => ∑ i, q.1 i • q.2 i
  have hf : Continuous f := by simp only [f]; fun_prop
  have hCclosed : IsClosed C := by
    rcases H with H | ⟨Z, W, hZ, hWc, hWcl, hXZ⟩
    · have hT : IsCompact (stdSimplex ℝ (Fin k) ×ˢ Set.univ.pi X) :=
        (isCompact_stdSimplex (𝕜 := ℝ) (ι := Fin k)).prod (isCompact_univ_pi fun i =>
          Metric.isCompact_of_isClosed_isBounded (H i).1 (H i).2)
      have : C = f '' (stdSimplex ℝ (Fin k) ×ˢ Set.univ.pi X) := by
        ext x
        constructor
        · intro hx
          obtain ⟨t, y, ht, hs, hy, rfl⟩ := hrep x (hCY hx)
          exact ⟨(t, y), ⟨⟨ht, hs⟩, fun i _ => hy i⟩, rfl⟩
        · rintro ⟨⟨t, y⟩, ⟨⟨ht, hs⟩, hy⟩, rfl⟩
          exact g70mc2_cc_mem X t y (fun i => hy i (Set.mem_univ _)) ht hs
      rw [this]; exact (hT.image hf).isClosed
    · have hT : IsCompact (stdSimplex ℝ (Fin k) ×ˢ Set.univ.pi Z) :=
        (isCompact_stdSimplex (𝕜 := ℝ) (ι := Fin k)).prod (isCompact_univ_pi fun i =>
          Metric.isCompact_of_isClosed_isBounded (hZ i).1 (hZ i).2)
      have : C = f '' (stdSimplex ℝ (Fin k) ×ˢ Set.univ.pi Z) + W := by
        ext x
        constructor
        · intro hx
          obtain ⟨t, y, ht, hs, hy, rfl⟩ := hrep x (hCY hx)
          have hy' : ∀ i, ∃ z ∈ Z i, ∃ w ∈ W, z + w = y i := fun i => by
            have := hy i; rw [hXZ i] at this; exact this
          choose z hz w hw e using hy'
          refine ⟨f (t, z), ⟨(t, z), ⟨⟨ht, hs⟩, fun i _ => hz i⟩, rfl⟩, ∑ i, t i • w i,
            hWc.sum_mem (fun i _ => ht i) hs (fun i _ => hw i), ?_⟩
          simp only [f, ← Finset.sum_add_distrib, ← smul_add, e]
        · intro hx
          obtain ⟨a, ha, w, hw, rfl⟩ := Set.mem_add.mp hx
          obtain ⟨⟨t, z⟩, ⟨htz, hz⟩, rfl⟩ := ha
          obtain ⟨ht, hs⟩ := htz
          have hmem : ∀ i, z i + w ∈ X i := fun i => by
            rw [hXZ i]; exact Set.add_mem_add (hz i (Set.mem_univ _)) hw
          have := g70mc2_cc_mem X t _ hmem ht hs
          convert this using 1
          simp only [f, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hs, one_smul]
      rw [this]; exact hWcl.add_left_of_isCompact (hT.image hf)
  refine ⟨hCeq, ?_, ?_⟩
  · rw [hCclosed.closure_eq, hCeq]
  · rw [hCeq]
    refine g70mc2_cqr_of_blocks (g70mc2_d K n) (g70mc2_d_pos K n) (g70mc2_L K p A B b)
      (g70mc2_c K) Y fun x => ?_
    constructor
    · rintro ⟨ξ, t, η, h1, h2, h3, h4⟩
      refine ⟨Sum.elim (fun q => ξ q.1 q.2) (Sum.elim t (fun q => η q.1 q.2)), ?_⟩
      rintro (⟨i, j'⟩ | i | a | ⟨⟩)
      · refine (g70mc2_condK K p A B b x _ i j').mpr ?_
        simpa using h1 i j'
      · refine (g70mc2_cond2 0 (t i) 0).mpr ?_
        simp [h2 i]
      · have : x a - ∑ i, ξ i a = 0 := by rw [← h3]; simp [Finset.sum_apply]
        refine (g70mc2_cond2 (x a - ∑ i, ξ i a) 0 0).mpr ?_
        simp [this]
      · refine (g70mc2_cond2 (∑ i, t i) 0 (fun r => if (r : ℕ) = 0 then -1 else 0)).mpr ?_
        simp [h4]
    · rintro ⟨u, hu⟩
      refine ⟨fun i a => u (.inl (i, a)), fun i => u (.inr (.inl i)),
        fun i c => u (.inr (.inr ⟨i, c⟩)), fun i j' => ?_, fun i => ?_, ?_, ?_⟩
      · exact (g70mc2_condK K p A B b x u i j').mp (hu (.inl ⟨i, j'⟩))
      · have := (g70mc2_cond2 0 (u (.inr (.inl i))) 0).mp (hu (.inr (.inl i)))
        simp at this
        exact this
      · ext a
        have := (g70mc2_cond2 (x a - ∑ i, u (.inl (i, a))) 0 0).mp (hu (.inr (.inr (.inl a))))
        simp only [Pi.zero_apply, add_zero] at this
        have h0 := abs_nonpos_iff.mp this
        rw [Finset.sum_apply]
        linarith
      · have := (g70mc2_cond2 (∑ i, u (.inr (.inl i))) 0
          (fun r => if (r : ℕ) = 0 then -1 else 0)).mp (hu (.inr (.inr (.inr ()))))
        simp only [Fin.val_zero, Fin.val_one, if_true, one_ne_zero, if_false, add_zero] at this
        have h0 := abs_nonpos_iff.mp this
        linarith
