-- Prove2me | solution 2 for Gomory69.Asymptotic.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:48:16.878019+00:00
-- url     : https://prove2.me/submissions/a68ba116-8bc9-41eb-a89a-ead7950e5e3d

import Mathlib
import Definitions.Def_Gomory69_Asymptotic_GroupPolyhedron
import Definitions.Def_Gomory69_Asymptotic_IntegerProgram
import Theorems.Thm_Gomory69_Asymptotic_sub_mem_basisCone
import Theorems.Thm_Gomory69_Asymptotic_theorem_2
import Theorems.Thm_Gomory69_Asymptotic_theorem_3

-- carved verbatim out of submission 2b2057a6-b504-47d4-af8a-917ba14f8ea6, lines 740-749

section
open Gomory69
open Gomory69.Asymptotic
open Matrix

theorem thm1_core {G : Type*} [AddCommGroup G] [Fintype G] (𝒩 : Finset G)
    (h𝒩 : (0 : G) ∉ 𝒩) (t : ↥𝒩 → ℕ) (ht : IsIrreducible 𝒩 t) :
    ∏ g : ↥𝒩, (1 + t g) ≤ Fintype.card G := by
  classical
  let S : Finset (↥𝒩 → ℕ) := Fintype.piFinset (fun g => Finset.range (t g + 1))
  have hcard : S.card = ∏ g : ↥𝒩, (1 + t g) := by
    simp [S, Fintype.card_piFinset, add_comm]
  let φ : (↥𝒩 → ℕ) → G := fun s => ∑ g, s g • (g : G)
  have hinj : Set.InjOn φ S := by
    intro s hs r hr h
    simp only [S, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range] at hs hr
    have := ht (fun g => (r g : ℤ)) (fun g => (s g : ℤ))
      (fun g => ⟨by positivity, by have := hr g; omega⟩)
      (fun g => ⟨by positivity, by have := hs g; omega⟩)
      (by simpa [φ, natCast_zsmul] using h.symm)
    funext g
    have := congrFun this g
    simpa using this
  have : S.card ≤ (Finset.univ : Finset G).card :=
    Finset.card_le_card_of_injOn φ (fun _ _ => Finset.mem_univ _) hinj
  rw [← hcard]; simpa using this

theorem one_add_sum_le_prod {ι : Type*} [Fintype ι] (t : ι → ℕ) :
    1 + ∑ i, t i ≤ ∏ i, (1 + t i) := by
  classical
  have : ∀ s : Finset ι, 1 + ∑ i ∈ s, t i ≤ ∏ i ∈ s, (1 + t i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      nlinarith [Nat.zero_le (t a), Nat.zero_le (∑ i ∈ s, t i)]
  exact this Finset.univ

theorem sum_le_core {G : Type*} [AddCommGroup G] [Fintype G] (𝒩 : Finset G)
    (h𝒩 : (0 : G) ∉ 𝒩) (t : ↥𝒩 → ℕ) (ht : IsIrreducible 𝒩 t) :
    ∑ g : ↥𝒩, t g ≤ Fintype.card G - 1 := by
  have h1 := thm1_core 𝒩 h𝒩 t ht
  have h2 := one_add_sum_le_prod t
  omega

theorem lattice_eq_range {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) :
    basisLattice B = (LinearMap.range (Matrix.mulVecLin B)).toAddSubgroup := by
  apply le_antisymm
  · unfold basisLattice
    rw [AddSubgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j 1, ?_⟩
    funext i
    simp [Matrix.mulVec_single_one]
  · rintro _ ⟨x, rfl⟩
    have : Matrix.mulVecLin B x = ∑ j, x j • (fun i => B i j) := by
      funext i
      simp [Matrix.mulVec, dotProduct, mul_comm]
    show Matrix.mulVecLin B x ∈ basisLattice B
    rw [this]
    refine AddSubgroup.sum_mem _ (fun j _ => ?_)
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self j)) _

theorem card_factor_core {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (hdet : B.det ≠ 0) :
    Finite (FactorGroup B) ∧ Nat.card (FactorGroup B) = detAbs B := by
  have hinj : Function.Injective (Matrix.mulVecLin B) := by
    intro x y hxy
    have : B.mulVec (x - y) = 0 := by
      rw [Matrix.mulVec_sub]; exact sub_eq_zero.mpr hxy
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hdet this
    exact sub_eq_zero.mp h2
  let e : (Fin m → ℤ) ≃ₗ[ℤ] LinearMap.range (Matrix.mulVecLin B) :=
    LinearEquiv.ofInjective (Matrix.mulVecLin B) hinj
  have h := Submodule.natAbs_det_equiv (LinearMap.range (Matrix.mulVecLin B)) e
  have hcomp : (LinearMap.range (Matrix.mulVecLin B)).subtype ∘ₗ
      AddMonoidHom.toIntLinearMap ((e : (Fin m → ℤ) →+ _)) = Matrix.mulVecLin B := by
    ext x : 1
    rfl
  have hd : LinearMap.det (Matrix.mulVecLin B) = B.det := by
    rw [← Matrix.toLin'_apply', LinearMap.det_toLin']
  have hcard : Nat.card ((Fin m → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)) = detAbs B := by
    rw [← h]
    unfold detAbs
    rw [hcomp, hd]
  have hfin : Finite ((Fin m → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    unfold detAbs
    exact Int.natAbs_ne_zero.mpr hdet
  have eq : FactorGroup B ≃ ((Fin m → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)) :=
    (QuotientAddGroup.quotientAddEquivOfEq (lattice_eq_range B)).toEquiv
  exact ⟨Finite.of_equiv _ eq.symm, by rw [Nat.card_congr eq]; exact hcard⟩

theorem euclNorm_smul' {m : ℕ} (s : ℝ) (v : Fin m → ℝ) : euclNorm (s • v) = |s| * euclNorm v := by
  unfold euclNorm
  have : ∑ k, (s • v) k ^ 2 = s ^ 2 * ∑ k, v k ^ 2 := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; simp [mul_pow]
  rw [this, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq_eq_abs]

end

section
open Gomory69
open Gomory69.Asymptotic
open Matrix
variable {m n : ℕ}

theorem zero_of_not_mem_colSet (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (i : Fin n) (h : groupColumn B N i ∉ groupColumnSet B N) : groupColumn B N i = 0 := by
  classical
  by_contra h0
  apply h
  unfold groupColumnSet
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩, h0⟩

theorem zero_not_mem_colSet (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ) :
    (0 : FactorGroup B) ∉ groupColumnSet B N := by
  classical
  unfold groupColumnSet
  simp

theorem fiber_total {α : Type*} [AddCommMonoid α] (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (F : Fin n → α) (hF : ∀ i, groupColumn B N i = 0 → F i = 0) :
    ∑ i, F i = ∑ g : ↥(groupColumnSet B N), ∑ i ∈ columnsOf B N (g : FactorGroup B), F i := by
  classical
  rw [Finset.sum_coe_sort (groupColumnSet B N) (fun g => ∑ i ∈ columnsOf B N g, F i)]
  have h1 : ∑ g ∈ groupColumnSet B N, ∑ i ∈ columnsOf B N g, F i
      = ∑ i ∈ Finset.univ.filter (fun i => groupColumn B N i ∈ groupColumnSet B N), F i := by
    have := Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter
      (fun i => groupColumn B N i ∈ groupColumnSet B N)) (t := groupColumnSet B N)
      (g := groupColumn B N) (f := F) (fun i hi => (Finset.mem_filter.1 hi).2)
    rw [← this]
    apply Finset.sum_congr rfl
    intro g hg
    apply Finset.sum_congr
    · ext i
      simp only [columnsOf, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; exact ⟨by rw [h]; exact hg, h⟩
      · intro h; exact h.2
    · intros; rfl
  rw [h1]
  symm
  apply Finset.sum_filter_of_ne
  intro i _ hne
  by_contra hn
  exact hne (hF i (zero_of_not_mem_colSet B N i hn))

theorem vertex_t (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hdet : B.det ≠ 0)
    (tstar : ↥(groupColumnSet B N) → ℝ)
    (ht : tstar ∈ Set.extremePoints ℝ (groupPolyhedron (groupColumnSet B N) (toGroup B b)))
    (xN : Fin n → ℕ) (hx : IsVertexLift B N tstar xN) :
    ∃ t : ↥(groupColumnSet B N) → ℕ, t ∈ groupSolutions (groupColumnSet B N) (toGroup B b) ∧
      IsIrreducible (groupColumnSet B N) t ∧ toReal _ t = tstar ∧
      ∀ g : ↥(groupColumnSet B N), ∑ i ∈ columnsOf B N (g : FactorGroup B), xN i = t g := by
  haveI := (card_factor_core B hdet).1
  obtain ⟨t, hts, htr, hirr⟩ := Gomory69.Asymptotic.theorem_2 _ (zero_not_mem_colSet B N) _ tstar ht
  refine ⟨t, hts, hirr, htr, fun g => ?_⟩
  have := hx.1 g
  rw [← htr] at this
  simp only [toReal] at this
  exact_mod_cast this

theorem euclNorm_add_le (u v : Fin m → ℝ) : euclNorm (u + v) ≤ euclNorm u + euclNorm v := by
  have h : ∀ w : Fin m → ℝ, euclNorm w = ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin m))‖ := by
    intro w
    rw [EuclideanSpace.norm_eq]
    simp [euclNorm]
  rw [h, h, h]
  have : (WithLp.toLp 2 (u + v) : EuclideanSpace ℝ (Fin m)) = WithLp.toLp 2 u + WithLp.toLp 2 v := rfl
  rw [this]
  exact norm_add_le _ _

theorem euclNorm_zero' : euclNorm (0 : Fin m → ℝ) = 0 := by simp [euclNorm]

theorem euclNorm_nonneg' (v : Fin m → ℝ) : 0 ≤ euclNorm v := Real.sqrt_nonneg _

theorem euclNorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → Fin m → ℝ) :
    euclNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, euclNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [euclNorm_zero']
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (euclNorm_add_le _ _) (add_le_add_right ih _)

theorem col_le_lmax (N : Matrix (Fin m) (Fin n) ℤ) (i : Fin n) :
    euclNorm (fun k => (N k i : ℝ)) ≤ lmax N :=
  le_ciSup (f := fun i : Fin n => euclNorm (fun k => (N k i : ℝ))) (Set.finite_range _).bddAbove i

theorem lmax_nonneg (N : Matrix (Fin m) (Fin n) ℤ) : 0 ≤ lmax N :=
  Real.iSup_nonneg (fun i => euclNorm_nonneg' _)

theorem card_eq_detAbs (B : Matrix (Fin m) (Fin m) ℤ) (hdet : B.det ≠ 0) [Fintype (FactorGroup B)] :
    Fintype.card (FactorGroup B) = detAbs B := by
  rw [← Nat.card_eq_fintype_card]; exact (card_factor_core B hdet).2

theorem detAbs_pos (B : Matrix (Fin m) (Fin m) ℤ) (hdet : B.det ≠ 0) : 1 ≤ detAbs B := by
  unfold detAbs; exact Int.natAbs_pos.2 hdet

theorem sum_xN_le (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hdet : B.det ≠ 0) (tstar : ↥(groupColumnSet B N) → ℝ)
    (ht : tstar ∈ Set.extremePoints ℝ (groupPolyhedron (groupColumnSet B N) (toGroup B b)))
    (xN : Fin n → ℕ) (hx : IsVertexLift B N tstar xN) :
    ∑ i, xN i ≤ detAbs B - 1 := by
  classical
  obtain ⟨t, hts, hirr, htr, hsum⟩ := vertex_t B N b hdet tstar ht xN hx
  haveI := (card_factor_core B hdet).1
  letI := Fintype.ofFinite (FactorGroup B)
  have h1 := sum_le_core _ (zero_not_mem_colSet B N) t hirr
  rw [card_eq_detAbs B hdet] at h1
  have h2 : ∑ i, xN i = ∑ g : ↥(groupColumnSet B N), t g := by
    rw [fiber_total B N xN (fun i h => hx.2.2 i h)]
    exact Finset.sum_congr rfl (fun g _ => hsum g)
  omega

theorem norm_le_core {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (hdet : B.det ≠ 0) (tstar : ↥(groupColumnSet B N) → ℝ)
    (ht : tstar ∈ Set.extremePoints ℝ (groupPolyhedron (groupColumnSet B N) (toGroup B b)))
    (xN : Fin n → ℕ) (hx : IsVertexLift B N tstar xN) :
    euclNorm (fun k => ∑ i, (N k i : ℝ) * (xN i : ℝ)) ≤ lmax N * ((detAbs B : ℝ) - 1) := by
  have hs := sum_xN_le B N b hdet tstar ht xN hx
  have hpos := detAbs_pos B hdet
  have hs' : (∑ i, (xN i : ℝ)) ≤ (detAbs B : ℝ) - 1 := by
    have : ((∑ i, xN i : ℕ) : ℝ) ≤ ((detAbs B - 1 : ℕ) : ℝ) := by exact_mod_cast hs
    rw [Nat.cast_sub hpos] at this
    simpa using this
  have hv : (fun k => ∑ i, (N k i : ℝ) * (xN i : ℝ)) = ∑ i, (xN i : ℝ) • (fun k => (N k i : ℝ)) := by
    funext k; simp [Finset.sum_apply, mul_comm]
  rw [hv]
  refine le_trans (euclNorm_sum_le _ _) ?_
  calc ∑ i, euclNorm ((xN i : ℝ) • fun k => (N k i : ℝ))
      = ∑ i, (xN i : ℝ) * euclNorm (fun k => (N k i : ℝ)) := by
        apply Finset.sum_congr rfl; intro i _
        rw [euclNorm_smul', abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ ∑ i, (xN i : ℝ) * lmax N := by
        apply Finset.sum_le_sum; intro i _
        exact mul_le_mul_of_nonneg_left (col_le_lmax N i) (Nat.cast_nonneg _)
    _ = (∑ i, (xN i : ℝ)) * lmax N := by rw [Finset.sum_mul]
    _ ≤ ((detAbs B : ℝ) - 1) * lmax N := mul_le_mul_of_nonneg_right hs' (lmax_nonneg N)
    _ = _ := by ring

theorem nonneg_core {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (hdet : B.det ≠ 0)
    (hb : realVec b ∈ deepCone B (lmax N * ((detAbs B : ℝ) - 1)))
    (tstar : ↥(groupColumnSet B N) → ℝ)
    (ht : tstar ∈ Set.extremePoints ℝ (groupPolyhedron (groupColumnSet B N) (toGroup B b)))
    (xN : Fin n → ℕ) (hx : IsVertexLift B N tstar xN) :
    ∀ k, 0 ≤ basicPart B N b xN k := by
  have hn := norm_le_core B N b hdet tstar ht xN hx
  have hmem := Gomory69.Asymptotic.sub_mem_basisCone B hdet _ (realVec b) (fun k => ∑ i, (N k i : ℝ) * (xN i : ℝ)) hb hn
  intro k
  have := hmem k
  have e : basicPart B N b xN = (realMatrix B)⁻¹ *ᵥ (realVec b - fun k => ∑ i, (N k i : ℝ) * (xN i : ℝ)) := by
    unfold basicPart realVec; rfl
  rw [e]; exact this

theorem thm4_core {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (c : Fin m ⊕ Fin n → ℝ)
    (hunit : ContainsUnitMatrix B N) (hdet : B.det ≠ 0) (hopt : IsOptimalLPBasis B N b c)
    (hb : realVec b ∈ deepCone B (lmax N * ((detAbs B : ℝ) - 1)))
    (tstar : ↥(groupColumnSet B N) → ℝ) (ht : IsMinimizingVertex B N b c tstar)
    (xN : Fin n → ℕ) (hx : IsCorrespondingVertex B N c tstar xN) :
    ∃ xB : Fin m → ℤ, (∀ k, (xB k : ℝ) = basicPart B N b xN k) ∧
      IsOptimal B N b c (Sum.elim xB (fun i => (xN i : ℤ))) :=
  Gomory69.Asymptotic.theorem_3 B N b c hunit hdet hopt tstar ht xN hx (nonneg_core B N b hdet hb tstar ht.1 xN hx.1)

end

section
open Gomory69.Asymptotic

theorem solution {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (c : Fin m ⊕ Fin n → ℝ)
    (hunit : ContainsUnitMatrix B N) (hdet : B.det ≠ 0) (hopt : IsOptimalLPBasis B N b c)
    (hb : realVec b ∈ deepCone B (lmax N * ((detAbs B : ℝ) - 1)))
    (tstar : ↥(groupColumnSet B N) → ℝ) (ht : IsMinimizingVertex B N b c tstar)
    (xN : Fin n → ℕ) (hx : IsCorrespondingVertex B N c tstar xN) :
    ∃ xB : Fin m → ℤ, (∀ k, (xB k : ℝ) = basicPart B N b xN k) ∧
      IsOptimal B N b c (Sum.elim xB (fun i => (xN i : ℤ))) := by
  exact thm4_core B N b c hunit hdet hopt hb tstar ht xN hx

end
