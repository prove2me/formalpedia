-- Prove2me | solution 1 for OAI.BassTrace.Sparse.vanishing_of_zero_strata_tf
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T23:08:34.229039+00:00
-- url     : https://prove2.me/submissions/c7be59f9-eb87-490c-bb1b-14419bf02abb

import Mathlib
import Definitions.Def_OAIQ113B002

section
-- module Solutions.OAIQ113_TFB.BassTrace_ExteriorChains
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Chains

open scoped BigOperators

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

lemma contraction_square (α : M →ₗ[R] R) (x : ExteriorAlgebra R M) :
    contraction α (contraction α x) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft α x

lemma cone_contraction (α : M →ₗ[R] R) {v : M} (hv : α v = 1)
    (x : ExteriorAlgebra R M) :
    contraction α (ExteriorAlgebra.ι R v * x) +
      ExteriorAlgebra.ι R v * contraction α x = x := by
  rw [contraction_ι_mul, hv, one_smul, sub_add_cancel]

variable (Y : Type*)

lemma boundary_square (x : Algebra Y) : boundary Y (boundary Y x) = 0 :=
  contraction_square _ x

end Chains

/-! Alternating functions on vertex labels extend to genuine linear maps on exterior chains. -/

namespace ChainHomotopy

open scoped BigOperators

open Oriented

variable {Y : Type*}

lemma average_augmentation {n : ℕ} (hn : n ≠ 0) (v : Fin n → Y) :
    Chains.augmentation Y (average n v) = 1 := by
  simp [average, Nat.cast_ne_zero.mpr hn]

lemma d_square (n : ℕ) (x : Degree Y (n+2)) : d n (d (n+1) x) = 0 := by
  ext
  exact Chains.boundary_square _ _

lemma d_cone_cycle (n : ℕ) (v : Y →₀ ℂ) (hv : Chains.augmentation Y v = 1)
    (x : Degree Y n) (hx : Chains.boundary Y x = 0) :
    d n (cone n v x) = x := by
  ext
  change Chains.boundary Y (ExteriorAlgebra.ι ℂ v * (x : Chains.Algebra Y)) = _
  have he : Chains.boundary Y (ExteriorAlgebra.ι ℂ v * (x : Chains.Algebra Y)) +
      ExteriorAlgebra.ι ℂ v * Chains.boundary Y x = (x : Chains.Algebra Y) :=
    Chains.cone_contraction (Chains.augmentation Y) hv (x : Chains.Algebra Y)
  simpa only [hx, mul_zero, add_zero] using he

end ChainHomotopy

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_Incidence
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace OrientedIncidence

section

open scoped BigOperators

open Oriented ChainHomotopy

variable {V : Type*} [LinearOrder V]

lemma vertices_range {n : ℕ} (s : Set.powersetCard V n) : Set.range (vertices s) = s.val :=
  Finset.range_orderEmbOfFin s.val s.property

lemma vertices_eraseFace {n : ℕ} (s : Set.powersetCard V (n+1)) (i : Fin (n+1)) :
    vertices (eraseFace s i) = i.succAboveOrderEmb.comp (vertices s) := by
  symm
  apply Finset.orderEmbOfFin_unique' (eraseFace s i).property
  intro j
  apply Finset.mem_erase.mpr
  exact ⟨fun h => Fin.succAbove_ne i j ((vertices s).injective h),vertices_mem s _⟩

lemma boundary_basis (n : ℕ) (s : Set.powersetCard V (n+1)) :
    d n (basis (Y := V) (n+1) s) =
      ∑ i : Fin (n+1), (-1 : ℂ)^i.val • basis n (eraseFace s i) := by
  rw [basis_eq_wedge,d_wedge]
  apply Finset.sum_congr rfl
  intro i _
  rw [basis_eq_wedge]
  congr 2
  exact congrArg (fun e : Fin n ↪o V => (e : Fin n → V)) (vertices_eraseFace s i).symm

lemma boundary_basis_coefficient (n : ℕ) (s : Set.powersetCard V (n+1))
    (t : Set.powersetCard V n) :
    (basis n).repr (d n (basis (Y := V) (n+1) s)) t =
      ∑ i : Fin (n+1), if eraseFace s i = t then (-1 : ℂ)^i.val else 0 := by
  simp only [boundary_basis,map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,
    Module.Basis.repr_self,Finsupp.single_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all

end

open scoped BigOperators

open Oriented ChainHomotopy

variable {V : Type*} [LinearOrder V] {n : ℕ}

lemma insert_eraseFace (s : Set.powersetCard V (n+1)) (i : Fin (n+1)) :
    insert (vertices s i) (eraseFace s i).val = s.val :=
  Finset.insert_erase (vertices_mem s i)

lemma eraseFace_neq (s : Set.powersetCard V (n+1)) (i : Fin (n+1)) :
    vertices s i ∉ (eraseFace s i).val := Finset.notMem_erase _ _

lemma incidence_pair_injective (t : Set.powersetCard V n)
    {a b : Set.powersetCard V (n+1) × Fin (n+1)}
    (ha : eraseFace a.1 a.2 = t) (hb : eraseFace b.1 b.2 = t)
    (he : vertices a.1 a.2 = vertices b.1 b.2) : a = b := by
  have hs : a.1 = b.1 := by
    apply Subtype.ext
    rw [← insert_eraseFace a.1 a.2,← insert_eraseFace b.1 b.2,ha,hb,he]
  apply Prod.ext hs
  exact (vertices b.1).injective (by simpa only [hs] using he)

lemma mem_apexes (F : Finset (Set.powersetCard V (n+1))) (t : Set.powersetCard V n) (u : V) :
    u ∈ apexes F t ↔ u ∉ t.val ∧ ∃ s ∈ F, s.val = insert u t.val := by
  constructor
  · intro h
    obtain ⟨⟨s,i⟩,hp,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hp,ht⟩ := Finset.mem_filter.mp hp
    have hs := (Finset.mem_product.mp hp).1
    refine ⟨ht ▸ eraseFace_neq s i,s,hs,?_⟩
    rw [← insert_eraseFace s i,ht]
  · rintro ⟨hu,s,hs,he⟩
    have hus : u ∈ s.val := he ▸ Finset.mem_insert_self _ _
    obtain ⟨i,rfl⟩ := (show u ∈ Set.range (vertices s) from (vertices_range s).symm ▸ hus)
    apply Finset.mem_image.mpr
    refine ⟨(s,i),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hs,Finset.mem_univ _⟩,?_⟩,rfl⟩
    apply Subtype.ext
    simp only [eraseFace_val,he,Finset.erase_insert hu]

lemma sum_incidencePairs (F : Finset (Set.powersetCard V (n+1))) (t : Set.powersetCard V n)
    {A : Type*} [AddCommMonoid A] (f : V → A) :
    ∑ p ∈ incidencePairs F t, f (vertices p.1 p.2) = ∑ u ∈ apexes F t, f u := by
  symm
  apply Finset.sum_image
  intro a ha b hb he
  exact incidence_pair_injective t (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 he

lemma boundary_sum_coefficient (F : Finset (Set.powersetCard V (n+1)))
    (w : Set.powersetCard V (n+1) → ℂ) (t : Set.powersetCard V n) :
    (basis n).repr (d n (∑ s ∈ F, w s • basis (n+1) s)) t =
      ∑ p ∈ incidencePairs F t, w p.1 * (-1 : ℂ)^p.2.val := by
  simp only [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul,
    boundary_basis_coefficient,Finset.mul_sum]
  rw [incidencePairs,Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

end OrientedIncidence

namespace Sparse.Orientation

section

open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma facetForm_vertex (n : ℕ) (v : Fin n → (Fin (n+1) → ℝ)) (j : Fin n) :
    facetForm n v (v j) = 0 := by
  rw [facetForm_apply]
  apply Matrix.det_zero_of_row_eq (i := 0) (j := j.succ) (Fin.succ_ne_zero j).symm
  simp

end

lemma det_cons_delete {n : ℕ} (v : Fin (n+1) → (Fin (n+1) → ℝ)) (i : Fin (n+1)) :
    Matrix.det (Fin.cons (v i) (fun j => v (i.succAbove j))) =
      (-1 : ℝ)^i.val * Matrix.det v := by
  have h := Matrix.detRowAlternating.neg_one_pow_smul_map_insertNth i (v i) (i.removeNth v)
  rw [Fin.insertNth_removeNth,Function.update_eq_self] at h
  change (-1 : ℤ) ^ i.val • Matrix.det v =
    Matrix.det (Fin.cons (v i) (fun j => v (i.succAbove j))) at h
  simpa only [zsmul_eq_mul,Int.cast_pow,Int.cast_neg,Int.cast_one] using h.symm

lemma realSign_negOnePow_mul (k : ℕ) (a : ℝ) :
    Real.sign ((-1 : ℝ)^k * a) = (-1 : ℝ)^k * Real.sign a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_neg_one,neg_mul,Real.sign_neg,ih,neg_mul]

lemma determinant_deletion_orientation {n : ℕ}
    (v : Fin (n+1) → (Fin (n+1) → ℝ)) (i : Fin (n+1)) :
    (Real.sign (Matrix.det v) : ℂ) * (-1 : ℂ)^i.val =
      (Real.sign (Matrix.det (Fin.cons (v i) (fun j => v (i.succAbove j)))) : ℂ) := by
  rw [det_cons_delete,realSign_negOnePow_mul]
  simp only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_one]
  exact mul_comm _ _

open scoped BigOperators

lemma det_cons_unit {n : ℕ} (v : Fin n → (Fin (n+1) → ℝ)) (i : Fin (n+1)) :
    Matrix.det (Fin.cons (Pi.single i 1) v) =
      (-1 : ℝ)^i.val * Matrix.det (fun j k => v j (i.succAbove k)) := by
  calc
    _ = ∑ j : Fin (n+1), (-1 : ℝ)^j.val * (if j = i then 1 else 0) *
        Matrix.det (fun a b => v a (j.succAbove b)) :=
      by
        have h := Matrix.det_succ_row_zero (Fin.cons (Pi.single i 1) v)
        change Matrix.det (Fin.cons (Pi.single i 1) v) =
          ∑ j : Fin (n+1), (-1 : ℝ)^j.val *
            (Pi.single i (1 : ℝ) : Fin (n+1) → ℝ) j *
            Matrix.det (fun a b => v a (j.succAbove b)) at h
        simpa only [Pi.single_apply] using h
    _ = _ := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [hji]
      · simp

lemma facetForm_on_unit {n : ℕ} (v : Fin n → (Fin (n+1) → ℝ)) (i : Fin (n+1)) :
    facetForm n v (Pi.single i 1) =
      (-1 : ℝ)^i.val * Matrix.det (fun j k => v j (i.succAbove k)) :=
  det_cons_unit v i

lemma facetForm_column_zero {n : ℕ} (v : Fin n → (Fin (n+1) → ℝ))
    (i : Fin (n+1)) (hi : ∀ j, v j i = 0) (k : Fin (n+1)) (hki : k ≠ i) :
    facetForm n v (Pi.single k 1) = 0 := by
  rw [facetForm_apply]
  apply Matrix.det_eq_zero_of_column_eq_zero i
  intro j
  cases j using Fin.cases with
  | zero => simp [hki.symm]
  | succ j => exact hi j

lemma linearMap_eq_coord_of_units {n : ℕ} (f : (Fin n → ℝ) →ₗ[ℝ] ℝ)
    (i : Fin n) (hf : ∀ k, k ≠ i → f (Pi.single k 1) = 0) (x : Fin n → ℝ) :
    f x = x i * f (Pi.single i 1) := by
  have hx : x = ∑ k : Fin n, x k • Pi.single k 1 := by
    funext j
    simp [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
  have hh := congrArg f hx
  rw [map_sum] at hh
  simp only [map_smul,smul_eq_mul] at hh
  rw [hh,Finset.sum_eq_single i]
  · intro k _ hki
    simp [hf k hki]
  · simp

lemma facet_boundary_term {n : ℕ} (v : Fin n → (Fin (n+1) → ℝ)) (i : Fin (n+1)) :
    (if ∀ k, k ≠ i → facetForm n v (Pi.single k 1) = 0
       then Real.sign (facetForm n v (Pi.single i 1)) else 0) =
    (if ∀ j, v j i = 0 then
       (-1 : ℝ)^i.val * Real.sign (Matrix.det (fun j k => v j (i.succAbove k))) else 0) := by
  by_cases hi : ∀ j, v j i = 0
  · rw [ite_eq_left hi,ite_eq_left (fun k hki => facetForm_column_zero v i hi k hki),
      facetForm_on_unit,realSign_negOnePow_mul]
  · rw [ite_eq_right hi]
    split_ifs with hf
    · have hz : facetForm n v (Pi.single i 1) = 0 := by
        by_contra hn
        apply hi
        intro j
        have h := linearMap_eq_coord_of_units (facetForm n v) i hf (v j)
        rw [facetForm_vertex] at h
        exact (mul_eq_zero.mp h.symm).resolve_right hn
      simp only [hz,Real.sign_zero]
    · rfl

end Sparse.Orientation

namespace Fundamental

open scoped BigOperators

open OrientedIncidence Oriented ChainHomotopy Sparse.Orientation

variable {V : Type*} [LinearOrder V] {n : ℕ}

lemma boundary_coefficient (F : Finset (Set.powersetCard V (n+1)))
    (p : V → (Fin (n+1) → ℝ)) (t : Set.powersetCard V n) :
    (basis n).repr (d n (chain F p)) t =
      ∑ u ∈ apexes F t, (Real.sign (facetForm n (fun i => p (vertices t i)) (p u)) : ℂ) := by
  rw [chain,boundary_sum_coefficient]
  rw [← sum_incidencePairs F t]
  apply Finset.sum_congr rfl
  intro a ha
  have ht := (Finset.mem_filter.mp ha).2
  rw [determinant_deletion_orientation]
  congr 2
  rw [facetForm_apply]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp only [Fin.cons_succ]
    have h := congrArg (fun e : Fin n ↪o V => e i) (vertices_eraseFace a.1 a.2)
    rw [ht] at h
    exact congrArg p h.symm

end Fundamental

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_FacetGeometry
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Two-sided facet incidence inside a single affine carrier, without a manifold hypothesis. -/

namespace BassTrace.Sparse

section

open Set Finset

open scoped Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma exists_weights_of_mem_affineSpan {s : Finset E} {v : E}
    (hv : v ∈ affineSpan ℝ (s : Set E)) :
    ∃ w : E → ℝ, ∑ x ∈ s, w x = 1 ∧ v = ∑ x ∈ s, w x • x := by
  classical
  have hv' : v ∈ affineSpan ℝ (Set.range (fun x : s => (x : E))) := by simpa using hv
  obtain ⟨w, hw, hvw⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hv'
  let w' : E → ℝ := fun x => if h : x ∈ s then w ⟨x, h⟩ else 0
  have hsum : ∑ x ∈ s, w' x = ∑ x : s, w x := by
    rw [← Finset.sum_attach]
    simp [w']
  refine ⟨w', hsum.trans hw, ?_⟩
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hw] at hvw
  rw [← Finset.sum_attach]
  simpa [w'] using hvw

lemma exists_small_positive_weights {I : Type*} (s : Finset I) (w : I → ℝ)
    {c : ℝ} (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ i ∈ s, 0 < δ * w i + (1-δ) * c := by
  have he : ∀ᶠ δ : ℝ in 𝓝 0, ∀ i ∈ s, 0 < δ * w i + (1-δ) * c := by
    apply (s.eventually_all).mpr
    intro i _
    have hcont : Continuous (fun δ : ℝ => δ * w i + (1-δ) * c) := by fun_prop
    exact hcont.continuousAt.eventually (eventually_gt_nhds (by simpa using hc))
  have he' := he.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hlt := (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  exact (hpos.and (hlt.and he')).exists

end

section

open Set Finset

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma same_side_cone_overlap [DecidableEq E] {F : Finset E} (hF : F.Nonempty) {u v : E}
    (huF : u ∉ F) (hvspan : v ∈ affineSpan ℝ ((insert u F : Finset E) : Set E))
    (f : E →ₗ[ℝ] ℝ) (b : ℝ) (hFb : ∀ x ∈ F, f x = b)
    (hu : b < f u) (hv : b < f v) :
    ∃ p, p ∈ convexHull ℝ ((insert u F : Finset E) : Set E) ∧
      p ∈ convexHull ℝ ((insert v F : Finset E) : Set E) ∧ b < f p := by
  classical
  obtain ⟨w, hw, hvw⟩ := exists_weights_of_mem_affineSpan hvspan
  have hsum : w u + ∑ x ∈ F, w x = 1 := by simpa [Finset.sum_insert huF] using hw
  have hfv : f v = w u * f u + (∑ x ∈ F, w x) * b := by
    rw [hvw, map_sum, Finset.sum_insert huF]
    simp only [map_smul, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun x hx => congrArg (w x * ·) (hFb x hx))]
    rw [Finset.sum_mul]
  have hwu : 0 < w u := by
    have he : f v - b = w u * (f u - b) := by linear_combination hfv + b * hsum
    have hm : 0 < w u * (f u - b) := he ▸ sub_pos.mpr hv
    exact (mul_pos_iff_of_pos_right (sub_pos.mpr hu)).mp hm
  let c : ℝ := (F.card : ℝ)⁻¹
  have hc : 0 < c := inv_pos.mpr (Nat.cast_pos.mpr hF.card_pos)
  have hcsum : ∑ _x ∈ F, c = 1 := by
    simp [c, ne_of_gt (Nat.cast_pos.mpr hF.card_pos : (0 : ℝ) < F.card)]
  let q : E := ∑ x ∈ F, c • x
  have hq : q ∈ convexHull ℝ (F : Set E) :=
    sum_weights_mem_convexHull F (fun _ _ => hc.le) hcsum
  have hfq : f q = b := by
    change f (∑ x ∈ F, c • x) = b
    simp only [map_sum, map_smul, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun x hx => congrArg (c * ·) (hFb x hx)),
      ← Finset.sum_mul, hcsum, one_mul]
  obtain ⟨δ, hδ, hδ1, hδw⟩ := exists_small_positive_weights F w hc
  let r : E → ℝ := fun x => if x = u then 0 else c
  have hrF (x : E) (hx : x ∈ F) : r x = c := by
    simp [r, ne_of_mem_of_not_mem hx huF]
  have hru : r u = 0 := by simp [r]
  have hrsum : ∑ x ∈ insert u F, r x = 1 := by
    rw [Finset.sum_insert huF, hru, zero_add]
    rw [Finset.sum_congr rfl hrF]
    exact hcsum
  have hrq : ∑ x ∈ insert u F, r x • x = q := by
    rw [Finset.sum_insert huF, hru, zero_smul, zero_add]
    exact Finset.sum_congr rfl (fun x hx => by rw [hrF x hx])
  let z : E → ℝ := fun x => δ * w x + (1-δ) * r x
  have hz : ∀ x ∈ insert u F, 0 ≤ z x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simp only [z, hru, mul_zero, add_zero]
      exact (mul_pos hδ hwu).le
    · simpa only [z, hrF x hx] using (hδw x hx).le
  have hzsum : ∑ x ∈ insert u F, z x = 1 := by
    simp only [z, Finset.sum_add_distrib, ← Finset.mul_sum, hw, hrsum]
    ring
  have hzp : ∑ x ∈ insert u F, z x • x = δ • v + (1-δ) • q := by
    simp only [z, add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum]
    rw [← hvw, hrq]
  refine ⟨δ • v + (1-δ) • q, ?_, ?_, ?_⟩
  · rw [← hzp]
    exact sum_weights_mem_convexHull _ hz hzsum
  · apply (convex_convexHull ℝ ((insert v F : Finset E) : Set E))
      (subset_convexHull ℝ _ (Finset.mem_insert_self v F))
      ((convexHull_mono (show (F : Set E) ⊆ ((insert v F : Finset E) : Set E) from
        Finset.subset_insert _ _)) hq) hδ.le (sub_nonneg.mpr hδ1.le)
    ring
  · simp only [map_add, map_smul, smul_eq_mul, hfq]
    nlinarith [mul_pos hδ (sub_pos.mpr hv)]

end

section

open Set Finset

open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma apex_notMem_affineSpan {F : Finset E} {u : E} (hu : u ∉ F)
    (h : AffineIndependent ℝ ((↑) : ↥(insert u F) → E)) :
    u ∉ affineSpan ℝ (F : Set E) := by
  let i : ↥(insert u F) := ⟨u, Finset.mem_insert_self _ _⟩
  have hnot := h.notMem_affineSpan_sdiff i Set.univ
  have he : ((↑) : ↥(insert u F) → E) '' (Set.univ \ {i}) = (F : Set E) := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      rcases Finset.mem_insert.mp j.property with hj' | hj'
      · exact False.elim (hj.2 (Set.mem_singleton_iff.mpr (Subtype.ext hj')))
      · exact hj'
    · intro hx
      refine ⟨⟨x, Finset.mem_insert_of_mem hx⟩, ⟨Set.mem_univ _, ?_⟩, rfl⟩
      intro hi
      have hxu : x = u := congrArg Subtype.val (Set.mem_singleton_iff.mp hi)
      exact hu (hxu ▸ hx)
  simpa only [he] using hnot

lemma exists_facet_form {F : Finset E} (hF : F.Nonempty) {u : E}
    (hu : u ∉ affineSpan ℝ (F : Set E)) :
    ∃ (f : E →ₗ[ℝ] ℝ) (b : ℝ), (∀ x ∈ F, f x = b) ∧ f u ≠ b := by
  obtain ⟨a, ha⟩ := hF
  have has : a ∈ affineSpan ℝ (F : Set E) := subset_affineSpan ℝ _ ha
  have hua : u - a ∉ (affineSpan ℝ (F : Set E)).direction := by
    simpa only [← AffineSubspace.vsub_right_mem_direction_iff_mem has u,
      vsub_eq_sub] using hu
  obtain ⟨f, hfu, hfker⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hua inferInstance
  refine ⟨f, f a, ?_, ?_⟩
  · intro x hx
    have hxa : x - a ∈ (affineSpan ℝ (F : Set E)).direction :=
      (AffineSubspace.vsub_right_mem_direction_iff_mem has x).mpr
        (subset_affineSpan ℝ _ hx)
    have hz : f (x-a) = 0 := by
      have hm : f (x-a) ∈ (affineSpan ℝ (F : Set E)).direction.map f :=
        Submodule.mem_map.mpr ⟨x-a, hxa, rfl⟩
      rw [hfker, Submodule.mem_bot] at hm
      exact hm
    simpa only [map_sub, sub_eq_zero] using hz
  · simpa only [map_sub, sub_ne_zero] using hfu

lemma affineForm_eq_on_convexHull {F : Finset E} (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (h : ∀ x ∈ F, f x = b) {p : E} (hp : p ∈ convexHull ℝ (F : Set E)) : f p = b := by
  have he : (F : Set E).EqOn f.toAffineMap (AffineMap.const ℝ E b) := h
  exact AffineMap.eqOn_affineSpan he (convexHull_subset_affineSpan _ hp)

lemma eq_of_facet_same_side (K : Geometry.SimplicialComplex ℝ E)
    {F : Finset E} (hF : F.Nonempty) {u v : E} (huF : u ∉ F) (hvF : v ∉ F)
    (huK : insert u F ∈ K.faces) (hvK : insert v F ∈ K.faces)
    (hspan : v ∈ affineSpan ℝ ((insert u F : Finset E) : Set E))
    (f : E →ₗ[ℝ] ℝ) (b : ℝ) (hFb : ∀ x ∈ F, f x = b)
    (hu : b < f u) (hv : b < f v) : u = v := by
  by_contra huv
  obtain ⟨p, hpu, hpv, hp⟩ := same_side_cone_overlap hF huF hspan f b hFb hu hv
  have hinter : ((insert u F : Finset E) : Set E) ∩
      ((insert v F : Finset E) : Set E) = (F : Set E) := by
    ext x
    simp only [Finset.coe_insert, Set.mem_inter_iff, Set.mem_insert_iff]
    aesop
  have hpf := K.inter_subset_convexHull huK hvK ⟨hpu, hpv⟩
  rw [hinter] at hpf
  exact (ne_of_gt hp) (affineForm_eq_on_convexHull f b hFb hpf)

lemma facet_apex_card_le_two (K : Geometry.SimplicialComplex ℝ E)
    {F A : Finset E} (hF : F.Nonempty)
    (hAK : ∀ u ∈ A, insert u F ∈ K.faces) (hAF : ∀ u ∈ A, u ∉ F)
    (hcarrier : ∀ u ∈ A, ∀ v ∈ A,
      affineSpan ℝ ((insert u F : Finset E) : Set E) =
        affineSpan ℝ ((insert v F : Finset E) : Set E)) : A.card ≤ 2 := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  obtain ⟨f, b, hFb, hab⟩ := exists_facet_form hF
    (apex_notMem_affineSpan (hAF a ha) (K.indep (hAK a ha)))
  have hne (u : E) (hu : u ∈ A) : f u ≠ b := by
    intro hub
    have hon : ((insert u F : Finset E) : Set E).EqOn
        f.toAffineMap (AffineMap.const ℝ E b) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hub
      · exact hFb x hx
    have he := AffineMap.eqOn_affineSpan hon
    apply hab
    apply he
    rw [hcarrier u hu a ha]
    exact subset_affineSpan ℝ _ (Finset.mem_insert_self _ _)
  let side : A → Bool := fun u => decide (b < f u)
  have hinj : Function.Injective side := by
    intro u v huv
    apply Subtype.ext
    have hs : (b < f u) ↔ (b < f v) := by
      exact decide_eq_decide.mp huv
    have hspan : (v : E) ∈ affineSpan ℝ ((insert (u : E) F : Finset E) : Set E) := by
      rw [hcarrier u u.property v v.property]
      exact subset_affineSpan ℝ _ (Finset.mem_insert_self _ _)
    by_cases hu : b < f u
    · exact eq_of_facet_same_side K hF (hAF u u.property) (hAF v v.property)
        (hAK u u.property) (hAK v v.property) hspan f b hFb hu (hs.mp hu)
    · have hv : ¬ b < f v := fun hv => hu (hs.mpr hv)
      have hul : f u < b := lt_of_le_of_ne (le_of_not_gt hu) (hne u u.property)
      have hvl : f v < b := lt_of_le_of_ne (le_of_not_gt hv) (hne v v.property)
      exact eq_of_facet_same_side K hF (hAF u u.property) (hAF v v.property)
        (hAK u u.property) (hAK v v.property) hspan (-f) (-b)
        (fun x hx => congrArg Neg.neg (hFb x hx))
        (neg_lt_neg hul) (neg_lt_neg hvl)
  simpa using Fintype.card_le_of_injective side hinj

lemma affineSpan_eq_of_card_eq {s t : Finset E}
    (ht : AffineIndependent ℝ ((↑) : t → E))
    (hst : (t : Set E) ⊆ convexHull ℝ (s : Set E)) (hc : t.card = s.card) :
    affineSpan ℝ (t : Set E) = affineSpan ℝ (s : Set E) := by
  have hle : affineSpan ℝ (t : Set E) ≤ affineSpan ℝ (s : Set E) :=
    affineSpan_le.mpr (hst.trans (convexHull_subset_affineSpan _))
  by_contra hne
  have hlt := ht.card_lt_card_of_affineSpan_lt_affineSpan (lt_of_le_of_ne hle hne)
  omega

lemma facet_coface_card_le_two (K : Geometry.SimplicialComplex ℝ E)
    {F S : Finset E} {B : Finset (Finset E)} (hF : F.Nonempty)
    (hS : S.card = F.card + 1) (hB : ∀ t ∈ B, t ∈ K.faces)
    (hFB : ∀ t ∈ B, F ⊆ t ∧ t.card = F.card + 1)
    (hBS : ∀ t ∈ B, (t : Set E) ⊆ convexHull ℝ (S : Set E)) : B.card ≤ 2 := by
  have hex (t : B) : ∃ u ∉ F, insert u F = (t : Finset E) :=
    Finset.exists_eq_insert_iff.mpr ⟨(hFB t t.property).1, (hFB t t.property).2.symm⟩
  let apex : B → E := fun t => (hex t).choose
  have ha (t : B) : apex t ∉ F ∧ insert (apex t) F = (t : Finset E) :=
    (hex t).choose_spec
  let A : Finset E := Finset.univ.image apex
  have hAK : ∀ u ∈ A, insert u F ∈ K.faces := by
    intro u hu
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hu
    rw [(ha t).2]
    exact hB t t.property
  have hAF : ∀ u ∈ A, u ∉ F := by
    intro u hu
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hu
    exact (ha t).1
  have hsp (u : E) (hu : u ∈ A) :
      affineSpan ℝ ((insert u F : Finset E) : Set E) = affineSpan ℝ (S : Set E) := by
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hu
    rw [(ha t).2]
    exact affineSpan_eq_of_card_eq (K.indep (hB t t.property)) (hBS t t.property)
      ((hFB t t.property).2.trans hS.symm)
  have hA := facet_apex_card_le_two K hF hAK hAF
    (fun u hu v hv => (hsp u hu).trans (hsp v hv).symm)
  have hinj : Function.Injective apex := by
    intro t t' he
    apply Subtype.ext
    calc (t : Finset E) = insert (apex t) F := (ha t).2.symm
         _ = insert (apex t') F := by rw [he]
         _ = (t' : Finset E) := (ha t').2
  have hc : A.card = B.card := by simp [A, Finset.card_image_of_injective _ hinj]
  rwa [hc] at hA

end

section

open Set Finset

open scoped Topology Classical

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma eventually_coface_at_positivePoint (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {F : Finset E} (hF : F ∈ K.faces)
    (w : E → ℝ) (hw : ∀ x ∈ F, 0 < w x) (hws : ∑ x ∈ F, w x = 1) :
    ∀ᶠ q in 𝓝 (∑ x ∈ F, w x • x),
      ∀ T ∈ K.faces, q ∈ convexHull ℝ (T : Set E) → F ⊆ T := by
  classical
  apply (hK.eventually_all).mpr
  intro T hT
  by_cases hFT : F ⊆ T
  · exact Filter.Eventually.of_forall (fun _ _ => hFT)
  · have hnot : (∑ x ∈ F, w x • x) ∉ convexHull ℝ (T : Set E) := by
      intro hq
      exact hFT (simplex_contains_positivePoint K hF hT w hw hws hq)
    have hc : IsClosed (convexHull ℝ (T : Set E)) := (T.finite_toSet.isCompact_convexHull ℝ).isClosed
    have he : ∀ᶠ q in 𝓝 (∑ x ∈ F, w x • x), q ∉ convexHull ℝ (T : Set E) :=
      hc.isOpen_compl.mem_nhds hnot
    exact he.mono (fun _ hq hh => False.elim (hq hh))

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_facet_coface_on_side (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hconv : Convex ℝ K.space)
    {F : Finset E} (hF : F ∈ K.faces)
    (hdim : ∀ T ∈ K.faces, T.card ≤ F.card+1)
    (f : E →ₗ[ℝ] ℝ) (b : ℝ) (hFb : ∀ x ∈ F, f x = b)
    {v : E} (hv : v ∈ K.space) (hfv : b < f v) :
    ∃ u ∉ F, insert u F ∈ K.faces ∧ b < f u := by
  classical
  have hFn := K.nonempty_of_mem_faces hF
  let c : ℝ := (F.card : ℝ)⁻¹
  have hc : 0 < c := inv_pos.mpr (Nat.cast_pos.mpr hFn.card_pos)
  have hcs : ∑ _x ∈ F, c = 1 := by
    simp [c,ne_of_gt (Nat.cast_pos.mpr hFn.card_pos : (0:ℝ) < F.card)]
  let q : E := ∑ x ∈ F, c • x
  have hqF : q ∈ convexHull ℝ (F : Set E) :=
    sum_weights_mem_convexHull F (fun _ _ => hc.le) hcs
  have hfq : f q = b := affineForm_eq_on_convexHull f b hFb hqF
  have hev := eventually_coface_at_positivePoint K hK hF (fun _ => c) (fun _ _ => hc) hcs
  have hcont : Continuous (fun δ : ℝ => δ • v + (1-δ) • q) := by fun_prop
  have hlim : Filter.Tendsto (fun δ : ℝ => δ • v + (1-δ) • q) (𝓝 0) (𝓝 q) := by
    simpa using hcont.continuousAt.tendsto (x := 0)
  have he := (hlim.eventually hev).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  have hlt := (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono
    (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ,hδ,hδ1,hδK⟩ := (hpos.and (hlt.and he)).exists
  have hδq : δ • v + (1-δ) • q ∈ K.space :=
    hconv hv (K.convexHull_subset_space hF hqF) hδ.le (sub_nonneg.mpr hδ1.le) (by ring)
  have hfδ : b < f (δ • v + (1-δ) • q) := by
    simp only [map_add,map_smul,smul_eq_mul,hfq]
    nlinarith [mul_pos hδ (sub_pos.mpr hfv)]
  obtain ⟨T,hT,hδT⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hδq
  have hFT := hδK T hT hδT
  have hne : F ≠ T := by
    intro heq
    subst T
    have heq := affineForm_eq_on_convexHull f b hFb hδT
    exact (ne_of_gt hfδ) heq
  have hcT : F.card+1 = T.card := by
    have hltc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hFT,hne⟩)
    have hh := hdim T hT
    omega
  obtain ⟨u,hu,rfl⟩ := Finset.exists_eq_insert_iff.mpr ⟨hFT,hcT⟩
  refine ⟨u,hu,hT,?_⟩
  by_contra hfu
  have hleft : convexHull ℝ ((insert u F : Finset E) : Set E) ⊆ {x | f x ≤ b} := by
    apply convexHull_min _ (convex_halfSpace_le f.isLinear b)
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_of_not_gt hfu
    · exact (hFb x hx).le
  exact (not_le_of_gt hfδ) (hleft hδT)

end

section

open Set Finset

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma convexHull_inter_supporting (S : Set E) (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (hS : ∀ x ∈ S, f x ≤ b) :
    convexHull ℝ S ∩ {x | f x = b} = convexHull ℝ (S ∩ {x | f x = b}) := by
  let T := convexHull ℝ (S ∩ {x | f x = b})
  let C := {x : E | f x ≤ b ∧ (f x = b → x ∈ T)}
  have hSC : S ⊆ C := by
    intro x hx
    exact ⟨hS x hx, fun he => subset_convexHull ℝ _ ⟨hx, he⟩⟩
  have hC : Convex ℝ C := by
    intro x hx y hy u v hu hv huv
    change f (u • x + v • y) ≤ b ∧ (f (u • x + v • y) = b → _)
    simp only [map_add, map_smul, smul_eq_mul]
    have hew : u*b + v*b = b := by rw [← add_mul, huv, one_mul]
    have hux : 0 ≤ u*(b-f x) := mul_nonneg hu (sub_nonneg.mpr hx.1)
    have hvy : 0 ≤ v*(b-f y) := mul_nonneg hv (sub_nonneg.mpr hy.1)
    refine ⟨?_, ?_⟩
    · nlinarith only [hew, hux, hvy]
    · intro he
      by_cases hu0 : u = 0
      · have hv1 : v = 1 := by linarith
        have hyb : f y = b := by simpa [hu0, hv1] using he
        simpa [hu0, hv1] using hy.2 hyb
      by_cases hv0 : v = 0
      · have hu1 : u = 1 := by linarith
        have hxb : f x = b := by simpa [hv0, hu1] using he
        simpa [hv0, hu1] using hx.2 hxb
      have hux0 : u*(b-f x) = 0 := by nlinarith only [he, hew, hux, hvy]
      have hvy0 : v*(b-f y) = 0 := by nlinarith only [he, hew, hux, hvy]
      have hxb : f x = b := (sub_eq_zero.mp ((mul_eq_zero.mp hux0).resolve_left hu0)).symm
      have hyb : f y = b := (sub_eq_zero.mp ((mul_eq_zero.mp hvy0).resolve_left hv0)).symm
      exact (convex_convexHull ℝ _) (hx.2 hxb) (hy.2 hyb) hu hv huv
  apply subset_antisymm
  · intro x hx
    exact (convexHull_min hSC hC hx.1).2 hx.2
  · intro x hx
    refine ⟨convexHull_mono Set.inter_subset_left hx, ?_⟩
    have he : (S ∩ {x | f x = b}).EqOn f.toAffineMap (AffineMap.const ℝ E b) := fun _ hy => hy.2
    exact AffineMap.eqOn_affineSpan he (convexHull_subset_affineSpan _ hx)

end

open Set Finset

open scoped Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma full_face_affineSpan (K : Geometry.SimplicialComplex ℝ E) {S T : Finset E}
    (hspace : K.space ⊆ convexHull ℝ (S : Set E)) (hT : T ∈ K.faces)
    (hc : T.card = S.card) : affineSpan ℝ (T : Set E) = affineSpan ℝ (S : Set E) :=
  affineSpan_eq_of_card_eq (K.indep hT) ((subset_convexHull ℝ _).trans
    ((K.convexHull_subset_space hT).trans hspace)) hc

lemma parent_card_bound (K : Geometry.SimplicialComplex ℝ E) {S : Finset E}
    (hspace : K.space ⊆ convexHull ℝ (S : Set E)) :
    ∀ T ∈ K.faces, T.card ≤ S.card := by
  intro T hT
  exact (K.indep hT).card_le_card_of_subset_affineSpan ((subset_convexHull ℝ _).trans
    ((K.convexHull_subset_space hT).trans (hspace.trans (convexHull_subset_affineSpan _))))

lemma facet_positive_apex_card (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {S F : Finset E}
    (hspace : K.space = convexHull ℝ (S : Set E)) (hF : F ∈ K.faces)
    (hc : F.card+1 = S.card) (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (hFb : ∀ x ∈ F, f x = b) :
    ((facetApexes K hK F).filter (fun u => b < f u)).card =
      if ∃ v ∈ S, b < f v then 1 else 0 := by
  let A := (facetApexes K hK F).filter (fun u => b < f u)
  have hAc : A.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro u hu v hv
    obtain ⟨huA,hu⟩ := Finset.mem_filter.mp hu
    obtain ⟨hvA,hv⟩ := Finset.mem_filter.mp hv
    obtain ⟨huF,huK⟩ := (mem_facetApexes K hK F u).mp huA
    obtain ⟨hvF,hvK⟩ := (mem_facetApexes K hK F v).mp hvA
    apply eq_of_facet_same_side K (K.nonempty_of_mem_faces hF) huF hvF huK hvK _ f b hFb hu hv
    rw [full_face_affineSpan K hspace.subset huK (by simp [Finset.card_insert_of_notMem huF,hc])]
    exact convexHull_subset_affineSpan _ (hspace ▸ K.convexHull_subset_space hvK
      (subset_convexHull ℝ _ (Finset.mem_insert_self _ _)))
  have hAn : A.Nonempty ↔ ∃ v ∈ S, b < f v := by
    constructor
    · rintro ⟨u,hu⟩
      obtain ⟨huA,hu⟩ := Finset.mem_filter.mp hu
      have huK := ((mem_facetApexes K hK F u).mp huA).2
      by_contra hn
      push Not at hn
      have hh : convexHull ℝ (S : Set E) ⊆ {x | f x ≤ b} :=
        convexHull_min hn (convex_halfSpace_le f.isLinear b)
      exact (not_le_of_gt hu) (hh (hspace ▸ K.convexHull_subset_space huK
        (subset_convexHull ℝ _ (Finset.mem_insert_self _ _))))
    · rintro ⟨v,hv,hfv⟩
      obtain ⟨u,hu,huK,hfu⟩ := exists_facet_coface_on_side K hK
        (hspace.symm ▸ convex_convexHull ℝ (S : Set E)) hF
        (fun T hT => hc ▸ parent_card_bound K hspace.subset T hT) f b hFb
        (hspace.symm ▸ subset_convexHull ℝ (S : Set E) hv) hfv
      exact ⟨u,Finset.mem_filter.mpr ⟨(mem_facetApexes K hK F u).mpr ⟨hu,huK⟩,hfu⟩⟩
  change A.card = _
  split_ifs with h
  · have := (hAn.mpr h).card_pos
    omega
  · have := not_congr hAn |>.mpr h
    simp only [Finset.not_nonempty_iff_eq_empty.mp this,Finset.card_empty]

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_FundamentalChains
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse

open Set Finset

open scoped Classical

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma sum_real_sign {A : Finset E} (f : E → ℝ) :
    ∑ u ∈ A, Real.sign (f u) =
      ((A.filter (fun u => 0 < f u)).card : ℝ) - ((A.filter (fun u => f u < 0)).card : ℝ) := by
  have he (u : E) : Real.sign (f u) =
      (if 0 < f u then (1 : ℝ) else 0) - (if f u < 0 then 1 else 0) := by
    rcases lt_trichotomy (f u) 0 with h | h | h
    · simp [Real.sign_of_neg h,h,not_lt_of_ge h.le]
    · simp [h]
    · simp [Real.sign_of_pos h,h,not_lt_of_ge h.le]
  simp_rw [he]
  rw [Finset.sum_sub_distrib,Finset.sum_boole,Finset.sum_boole]

lemma signed_facet_incidence (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {S F : Finset E}
    (hspace : K.space = convexHull ℝ (S : Set E)) (hF : F ∈ K.faces)
    (hc : F.card+1 = S.card) (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (hFb : ∀ x ∈ F, f x = b) :
    ∑ u ∈ facetApexes K hK F, Real.sign (f u-b) =
      (if ∃ v ∈ S, b < f v then (1:ℝ) else 0) -
      (if ∃ v ∈ S, f v < b then (1:ℝ) else 0) := by
  rw [sum_real_sign]
  simp only [sub_pos,sub_neg]
  rw [facet_positive_apex_card K hK hspace hF hc f b hFb]
  have hn := facet_positive_apex_card K hK hspace hF hc (-f) (-b)
    (fun x hx => by simp [hFb x hx])
  simp only [LinearMap.neg_apply,neg_lt_neg_iff] at hn
  rw [hn]
  split_ifs <;> norm_num

lemma one_sided_parent_unique {S F : Finset E}
    (hF : AffineIndependent ℝ ((↑) : F → E)) (hc : F.card+1 = S.card)
    (hFS : (F : Set E) ⊆ convexHull ℝ (S : Set E))
    (f : E →ₗ[ℝ] ℝ) (b : ℝ) (hFb : ∀ x ∈ F, f x = b)
    (hSb : ∀ x ∈ S, f x ≤ b) (hne : ∃ x ∈ S, f x ≠ b) :
    ∃! v, v ∈ S ∧ f v ≠ b := by
  let T := S.filter (fun x => f x = b)
  have hFT : (F : Set E) ⊆ convexHull ℝ (T : Set E) := by
    intro x hx
    have hh : x ∈ convexHull ℝ (S : Set E) ∩ {x | f x = b} := ⟨hFS hx,hFb x hx⟩
    rw [convexHull_inter_supporting (S : Set E) f b hSb] at hh
    have heq : (S : Set E) ∩ {x | f x = b} = (T : Set E) := by
      ext y
      simp only [T,Set.mem_inter_iff,Set.mem_ofPred,Finset.mem_coe,Finset.mem_filter]
    rw [heq] at hh
    exact hh
  have hcard := hF.card_le_card_of_subset_affineSpan (hFT.trans (convexHull_subset_affineSpan _))
  have hcount := Finset.card_filter_add_card_filter_not (s := S) (fun x => f x = b)
  have hnot : (S.filter (fun x => f x ≠ b)).Nonempty := by
    obtain ⟨x,hx,hnx⟩ := hne
    exact ⟨x,Finset.mem_filter.mpr ⟨hx,hnx⟩⟩
  have hone : (S.filter (fun x => f x ≠ b)).card = 1 := by
    have := hnot.card_pos
    change T.card + (S.filter (fun x => f x ≠ b)).card = S.card at hcount
    omega
  obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hone
  refine ⟨v,?_,?_⟩
  · have : v ∈ S.filter (fun x => f x ≠ b) := hv ▸ Finset.mem_singleton_self v
    exact Finset.mem_filter.mp this
  · intro w hw
    have : w ∈ S.filter (fun x => f x ≠ b) := Finset.mem_filter.mpr hw
    rw [hv,Finset.mem_singleton] at this
    exact this

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma parent_boundary_sign_sum {S F : Finset E}
    (hF : AffineIndependent ℝ ((↑) : F → E)) (hc : F.card+1 = S.card)
    (hFS : (F : Set E) ⊆ convexHull ℝ (S : Set E))
    (f : E →ₗ[ℝ] ℝ) (b : ℝ) (hFb : ∀ x ∈ F, f x = b) :
    ∑ v ∈ S, (if ∀ w ∈ S, w ≠ v → f w = b then Real.sign (f v-b) else 0) =
      (if ∃ v ∈ S, b < f v then (1:ℝ) else 0) -
      (if ∃ v ∈ S, f v < b then (1:ℝ) else 0) := by
  by_cases hp : ∃ v ∈ S, b < f v
  · obtain ⟨p,hpS,hpv⟩ := hp
    by_cases hn : ∃ v ∈ S, f v < b
    · obtain ⟨q,hqS,hqv⟩ := hn
      have hpq : p ≠ q := by intro h; subst q; linarith
      have hz (v : E) (_ : v ∈ S) :
          (if ∀ w ∈ S, w ≠ v → f w = b then Real.sign (f v-b) else 0) = 0 := by
        have hh : ¬ ∀ w ∈ S, w ≠ v → f w = b := by
          intro hh
          by_cases hv : p = v
          · have := hh q hqS (by simpa [← hv] using hpq.symm)
            linarith
          · have := hh p hpS hv
            linarith
        simp only [hh,ite_false, if_false]
      rw [Finset.sum_eq_zero hz]
      simp only [show ∃ v ∈ S, b < f v from ⟨p,hpS,hpv⟩,
        show ∃ v ∈ S, f v < b from ⟨q,hqS,hqv⟩,ite_true, if_true,sub_self]
    · have hs : ∀ w ∈ S, b ≤ f w := by
        intro w hw
        exact le_of_not_gt (fun hh => hn ⟨w,hw,hh⟩)
      obtain ⟨v,⟨hv,hvn⟩,huniq⟩ := one_sided_parent_unique hF hc hFS (-f) (-b)
        (fun x hx => by simp [hFb x hx])
        (fun x hx => by simpa only [LinearMap.neg_apply,neg_le_neg_iff] using hs x hx)
        ⟨p,hpS,by intro he; have hh : -f p = -b := he; linarith⟩
      have hvp : b < f v := by
        have hvne : f v ≠ b := by intro he; apply hvn; simp only [LinearMap.neg_apply,he]
        exact lt_of_le_of_ne (hs v hv) hvne.symm
      have hzero (w : E) (hw : w ∈ S) (hwv : w ≠ v) : f w = b := by
        by_contra hh
        exact hwv (huniq w ⟨hw,by intro he; have he : -f w = -b := he; exact hh (by linarith)⟩)
      rw [Finset.sum_eq_single v]
      · rw [ite_eq_left hzero]
        simp only [ite_true, if_true,Real.sign_of_pos (sub_pos.mpr hvp),
          show ∃ v ∈ S, b < f v from ⟨p,hpS,hpv⟩,hn,ite_false, if_false,sub_zero]
      · intro w hw hwv
        simp only [hzero w hw hwv,sub_self,Real.sign_zero,ite_self]
      · exact fun hh => (hh hv).elim
  · by_cases hn : ∃ v ∈ S, f v < b
    · obtain ⟨q,hqS,hqv⟩ := hn
      have hs : ∀ w ∈ S, f w ≤ b := by
        intro w hw
        exact le_of_not_gt (fun hh => hp ⟨w,hw,hh⟩)
      obtain ⟨v,⟨hv,hvn⟩,huniq⟩ := one_sided_parent_unique hF hc hFS f b hFb hs
        ⟨q,hqS,ne_of_lt hqv⟩
      have hvn : f v < b := lt_of_le_of_ne (hs v hv) hvn
      have hzero (w : E) (hw : w ∈ S) (hwv : w ≠ v) : f w = b := by
        by_contra hh
        exact hwv (huniq w ⟨hw,hh⟩)
      rw [Finset.sum_eq_single v]
      · rw [ite_eq_left hzero]
        simp only [ite_true, if_true,Real.sign_of_neg (sub_neg.mpr hvn),hp,
          show ∃ v ∈ S, f v < b from ⟨q,hqS,hqv⟩,ite_false, if_false,zero_sub]
      · intro w hw hwv
        simp only [hzero w hw hwv,sub_self,Real.sign_zero,ite_self]
      · exact fun hh => (hh hv).elim
    · have hs (w : E) (hw : w ∈ S) : f w = b :=
        le_antisymm (le_of_not_gt (fun hh => hp ⟨w,hw,hh⟩))
          (le_of_not_gt (fun hh => hn ⟨w,hw,hh⟩))
      rw [Finset.sum_eq_zero (fun w hw => by
        simp only [hs w hw,sub_self,Real.sign_zero,ite_self])]
      simp only [hp,hn,ite_false, if_false,sub_self]

lemma signed_facet_boundary (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {S F : Finset E}
    (hspace : K.space = convexHull ℝ (S : Set E)) (hF : F ∈ K.faces)
    (hc : F.card+1 = S.card) (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (hFb : ∀ x ∈ F, f x = b) :
    ∑ u ∈ facetApexes K hK F, Real.sign (f u-b) =
      ∑ v ∈ S, (if ∀ w ∈ S, w ≠ v → f w = b then Real.sign (f v-b) else 0) := by
  rw [signed_facet_incidence K hK hspace hF hc f b hFb]
  symm
  exact parent_boundary_sign_sum (K.indep hF) hc
    (fun x hx => hspace ▸ K.convexHull_subset_space hF (subset_convexHull ℝ _ hx)) f b hFb

end Sparse

namespace Fundamental

section

open scoped BigOperators

open OrientedIncidence Oriented ChainHomotopy Sparse.Orientation

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]

lemma apexes_faces (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {n : ℕ} (t : Set.powersetCard E n) :
    apexes (faces K hK (n+1)) t = Sparse.facetApexes K hK t.val := by
  classical
  ext u
  rw [mem_apexes,Sparse.mem_facetApexes]
  constructor
  · rintro ⟨hu,s,hs,he⟩
    refine ⟨hu,?_⟩
    convert (mem_faces K hK _ s).mp hs using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp [he]
  · rintro ⟨hu,hs⟩
    refine ⟨hu,⟨insert u t.val,?_⟩,?_,rfl⟩
    · simp [Finset.card_insert_of_notMem hu]
    · apply (mem_faces K hK _ _).mpr
      convert hs using 1
      all_goals try with_reducible_and_instances rfl
      ext x
      simp

theorem geometric_boundary_coefficient (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {n : ℕ} {S : Finset E}
    (hspace : K.space = convexHull ℝ (S : Set E)) (hc : S.card = n+1)
    (p : E →ₗ[ℝ] (Fin (n+1) → ℝ)) (t : Set.powersetCard E n) (ht : t.val ∈ K.faces) :
    (basis n).repr (d n (chain (faces K hK (n+1)) p)) t =
      ∑ v ∈ S, (if ∀ w ∈ S, w ≠ v → facetForm n (fun i => p (vertices t i)) (p w) = 0
        then (Real.sign (facetForm n (fun i => p (vertices t i)) (p v)) : ℂ) else 0) := by
  rw [boundary_coefficient,apexes_faces]
  let f : E →ₗ[ℝ] ℝ := (facetForm n (fun i => p (vertices t i))).comp p
  have hf (x : E) (hx : x ∈ t.val) : f x = 0 := by
    obtain ⟨i,rfl⟩ := (show x ∈ Set.range (vertices t) from (vertices_range t).symm ▸ hx)
    exact facetForm_vertex n (fun i => p (vertices t i)) i
  have hh := Sparse.signed_facet_boundary K hK hspace ht (by rw [t.property,hc]) f 0 hf
  have hh := congrArg (fun r : ℝ => (r : ℂ)) hh
  simpa only [Complex.ofReal_sum,Complex.ofReal_sub,Complex.ofReal_zero,sub_zero,
    f,LinearMap.comp_apply,apply_ite,Complex.ofReal_zero] using hh

end

section

variable {V : Type*} [LinearOrder V]

lemma chain_coefficient {n : ℕ} (F : Finset (Set.powersetCard V (n+1)))
    (p : V → (Fin (n+1) → ℝ)) (t : Set.powersetCard V (n+1)) :
    (basis (n+1)).repr (chain F p) t =
      if t ∈ F then (Real.sign (Matrix.det (fun j => p (vertices t j))) : ℂ) else 0 := by
  simp only [chain,map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,
    Module.Basis.repr_self,Finsupp.single_apply,smul_eq_mul,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq']

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]

lemma boundary_coefficient_nonface (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {n : ℕ} (p : E → (Fin (n+2) → ℝ))
    (t : Set.powersetCard E (n+1)) (ht : t.val ∉ K.faces) :
    (basis (n+1)).repr (d (n+1) (chain (faces K hK (n+2)) p)) t = 0 := by
  classical
  rw [boundary_coefficient]
  have hem : apexes (faces K hK (n+2)) t = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    obtain ⟨_,s,hs,he⟩ := (mem_apexes _ t u).mp hu
    apply ht
    apply K.down_closed ((mem_faces K hK _ s).mp hs)
    · intro x hx
      rw [he]
      exact Finset.mem_insert_of_mem hx
    · exact Finset.card_pos.mp (by rw [t.property]; omega)
  rw [hem,Finset.sum_empty]

open scoped Classical

lemma faceChain_coefficient (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {n : ℕ} (p : E → (Fin (n+2) → ℝ)) (i : Fin (n+2)) (t : Set.powersetCard E (n+1)) :
    (basis (n+1)).repr (faceChain K hK p i) t =
      if t.val ∈ K.faces ∧ ∀ j, p (vertices t j) i = 0 then
        (Real.sign (Matrix.det (fun j k => p (vertices t j) (i.succAbove k))) : ℂ) else 0 := by
  classical
  rw [faceChain,chain_coefficient]
  congr 1
  rw [Finset.mem_filter,mem_faces]
  congr 1
  apply propext
  constructor
  · exact fun h j => h _ (vertices_mem t j)
  · intro h x hx
    obtain ⟨j,rfl⟩ := (show x ∈ Set.range (vertices t) from (vertices_range t).symm ▸ hx)
    exact h j

end

open scoped BigOperators Classical

open OrientedIncidence Oriented ChainHomotopy Sparse.Orientation

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma sum_enumeration {k : ℕ} (S : Finset E) (v : Fin k ↪ E)
    (hv : Set.range v = S) {A : Type*} [AddCommMonoid A] (f : E → A) :
    (∑ x ∈ S, f x) = ∑ i : Fin k, f (v i) := by
  have he : Finset.univ.image v = S := by
    apply Finset.coe_injective
    simpa only [Finset.coe_image,Finset.coe_univ,Set.image_univ] using hv
  rw [← he,Finset.sum_image v.injective.injOn]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E] in
lemma forall_enumeration_except {k : ℕ} (S : Finset E) (v : Fin k ↪ E)
    (hv : Set.range v = S) (i : Fin k) (P : E → Prop) :
    (∀ x ∈ S, x ≠ v i → P x) ↔ ∀ j, j ≠ i → P (v j) := by
  constructor
  · intro h j hji
    exact h _ (show v j ∈ (S : Set E) from hv ▸ Set.mem_range_self j) (fun he => hji (v.injective he))
  · intro h x hx hxi
    obtain ⟨j,rfl⟩ := (show x ∈ Set.range v from hv.symm ▸ hx)
    exact h j (fun he => hxi (congrArg v he))

theorem boundary_chain_chart (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {n : ℕ} (S : Finset E) (v : Fin (n+2) ↪ E) (hv : Set.range v = S)
    (hspace : K.space = convexHull ℝ (S : Set E))
    (p : E →ₗ[ℝ] (Fin (n+2) → ℝ))
    (hp : ∀ i, p (v i) = Pi.single i 1) :
    d (n+1) (chain (faces K hK (n+2)) p) =
      ∑ i : Fin (n+2), (-1 : ℂ)^i.val • faceChain K hK p i := by
  have hcard : S.card = n+2 := by
    have he : Finset.univ.image v = S := by
      apply Finset.coe_injective
      simpa only [Finset.coe_image,Finset.coe_univ,Set.image_univ] using hv
    rw [← he]
    simpa using Finset.card_image_of_injective Finset.univ v.injective
  apply (basis (n+1)).repr.injective
  apply Finsupp.ext
  intro t
  simp only [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul,
    faceChain_coefficient]
  by_cases ht : t.val ∈ K.faces
  · rw [geometric_boundary_coefficient K hK hspace hcard p t ht,sum_enumeration S v hv]
    simp only [ht,true_and]
    apply Finset.sum_congr rfl
    intro i _
    simp only [forall_enumeration_except S v hv, hp]
    have hh := congrArg (fun r : ℝ => (r : ℂ))
      (facet_boundary_term (fun j => p (vertices t j)) i)
    simpa only [apply_ite,Complex.ofReal_zero,Complex.ofReal_mul,Complex.ofReal_pow,
      Complex.ofReal_neg,Complex.ofReal_one,mul_ite,mul_zero] using hh
  · rw [boundary_coefficient_nonface K hK p t ht]
    simp only [ht,false_and,ite_false, if_false,mul_zero,Finset.sum_const_zero]

end

section

variable {V : Type*}

lemma term_perm (n : ℕ) (p : V → (Fin n → ℝ)) (v : Fin n → V)
    (σ : Equiv.Perm (Fin n)) : term n p (v ∘ σ) = term n p v := by
  unfold term
  have hdet : Matrix.det (fun j => p (v (σ j))) =
      (Equiv.Perm.sign σ : ℝ) * Matrix.det (fun j => p (v j)) := by
    have hh := Matrix.detRowAlternating.map_perm (fun j => p (v j)) σ
    change Matrix.det (fun j => p (v (σ j))) =
      (Equiv.Perm.sign σ) • Matrix.det (fun j => p (v j)) at hh
    simpa only [Units.smul_def,zsmul_eq_mul] using hh
  rw [wedge_perm]
  change (Real.sign (Matrix.det (fun j => p (v (σ j)))) : ℂ) •
    ((Equiv.Perm.sign σ) • wedge n v) = _
  rw [hdet]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with he | he
  · simp [he]
  · simp only [he,Int.cast_neg,Int.cast_one,Units.val_neg,Units.val_one,neg_one_mul,
      Real.sign_neg,Complex.ofReal_neg,neg_smul_neg,Units.neg_smul,one_smul]

end

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma parent_face_chart {n : ℕ} (v : Fin (n+1) → E)
    (p : E →ₗ[ℝ] (Fin (n+1) → ℝ)) (hp : ∀ j, p (v j) = Pi.single j 1)
    (i : Fin (n+1)) :
    convexHull ℝ (Set.range v) ∩ {x | p x i = 0} =
      convexHull ℝ (Set.range (fun j => v (i.succAbove j))) := by
  have hs : Set.range v ∩ {x | p x i = 0} =
      Set.range (fun j => v (i.succAbove j)) := by
    ext x
    constructor
    · rintro ⟨⟨j,rfl⟩,hj⟩
      have hji : j ≠ i := by
        intro he
        subst j
        change p (v i) i = 0 at hj
        simp only [hp,Pi.single_eq_same,one_ne_zero] at hj
      obtain ⟨k,hk⟩ := Fin.exists_succAbove_eq hji
      exact ⟨k,congrArg v hk⟩
    · rintro ⟨j,rfl⟩
      exact ⟨⟨i.succAbove j,rfl⟩,by simp [hp]⟩
  have hh := Sparse.convexHull_inter_supporting (Set.range v)
    (-((LinearMap.proj i).comp p)) 0 (by
      rintro _ ⟨j,rfl⟩
      change -(p (v j) i) ≤ 0
      simp only [hp,Pi.single_apply]
      split_ifs <;> norm_num)
  simp only [LinearMap.neg_apply,LinearMap.comp_apply,LinearMap.proj_apply,neg_eq_zero] at hh
  exact hh.trans (congrArg (convexHull ℝ) hs)

end Fundamental

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_ChainMaps
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Fundamental

open scoped BigOperators Classical

open OrientedIncidence Oriented ChainHomotopy Sparse.Orientation

variable {V W : Type*} [LinearOrder V] [LinearOrder W]

lemma term_eq_sorted {n : ℕ} (s : Set.powersetCard V n)
    (p : V → (Fin n → ℝ)) (v : Fin n → V) (hi : Function.Injective v)
    (hv : Set.range v = s.val) :
    term n p v = (Real.sign (Matrix.det (fun j => p (vertices s j))) : ℂ) • basis n s := by
  obtain ⟨t,σ,he⟩ := exists_sorted_perm v hi
  have hts : t = s := by
    apply Subtype.ext
    apply Finset.coe_injective
    rw [← vertices_range t,← hv,he]
    exact (σ.surjective.range_comp (vertices t)).symm
  subst t
  rw [he,term_perm]
  rw [basis_eq_wedge]
  rfl

omit [LinearOrder W] in
lemma simplexMap_range (f : V ↪ W) {n : ℕ} (s : Set.powersetCard V n) :
    Set.range (f ∘ vertices s) = (simplexMap f n s).val := by
  ext y
  constructor
  · rintro ⟨j,rfl⟩
    exact Finset.mem_map.mpr ⟨vertices s j,vertices_mem s j,rfl⟩
  · intro hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hy
    obtain ⟨j,rfl⟩ := (show x ∈ Set.range (vertices s) from (vertices_range s).symm ▸ hx)
    exact ⟨j,rfl⟩

lemma chain_relabel {n : ℕ} (F : Finset (Set.powersetCard V (n+1)))
    (p : V → (Fin (n+1) → ℝ)) (q : W → (Fin (n+1) → ℝ))
    (f : V ↪ W) (hpq : ∀ x, q (f x) = p x) :
    relabel (n+1) f (chain F p) = chain (F.map (simplexMap f (n+1))) q := by
  simp only [chain,map_sum,Finset.sum_map]
  apply Finset.sum_congr rfl
  intro s _
  rw [basis_eq_wedge,map_smul,relabel_wedge]
  have hh := term_eq_sorted (simplexMap f (n+1) s) q (f ∘ vertices s)
    (f.injective.comp (vertices s).injective) (simplexMap_range f s)
  simpa only [term,Function.comp_apply,hpq] using hh

end Fundamental

namespace Fundamental

open scoped BigOperators Classical

open OrientedIncidence Oriented ChainHomotopy Sparse.Orientation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]

lemma faceChain_eq_restrict (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {n : ℕ} (p : E → (Fin (n+2) → ℝ)) (i : Fin (n+2)) :
    faceChain K hK p i = chain
      (faces (Sparse.restrictComplex K {x | p x i = 0})
        (Sparse.restrictComplex_finite K _ hK) (n+1)) (fun x j => p x (i.succAbove j)) := by
  unfold faceChain
  congr 1
  ext s
  simp only [Finset.mem_filter,mem_faces,Sparse.restrictComplex]
  rfl

theorem boundary_chain_restrictions (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {n : ℕ} (S : Finset E) (v : Fin (n+2) ↪ E)
    (hv : Set.range v = S) (hspace : K.space = convexHull ℝ (S : Set E))
    (p : E →ₗ[ℝ] (Fin (n+2) → ℝ)) (hp : ∀ i, p (v i) = Pi.single i 1) :
    d (n+1) (chain (faces K hK (n+2)) p) =
      ∑ i : Fin (n+2), (-1 : ℂ)^i.val • chain
        (faces (Sparse.restrictComplex K {x | p x i = 0})
          (Sparse.restrictComplex_finite K _ hK) (n+1))
        (fun x j => p x (i.succAbove j)) := by
  rw [boundary_chain_chart K hK S v hv hspace p hp]
  simp only [faceChain_eq_restrict]

omit [LinearOrder E] in

lemma faces_one_of_space_singleton (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (x : E) (hspace : K.space = {x}) :
    faces K hK 1 = {⟨{x},by simp⟩} := by
  ext s
  rw [mem_faces,Finset.mem_singleton]
  constructor
  · intro hs
    apply Subtype.ext
    apply Finset.eq_singleton_iff_unique_mem.mpr
    have hsub : (s.val : Set E) ⊆ {x} := hspace ▸ K.subset_space hs
    obtain ⟨y,hy⟩ := K.nonempty_of_mem_faces hs
    have hyx : y=x := hsub hy
    subst y
    exact ⟨hy,fun _ hz => hsub hz⟩
  · rintro rfl
    have hx : x ∈ K.space := hspace.symm ▸ Set.mem_singleton x
    obtain ⟨s,hs,hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    have hsub : (s : Set E) ⊆ {x} := hspace ▸ K.subset_space hs
    obtain ⟨y,hy⟩ := K.nonempty_of_mem_faces hs
    have hyx : y=x := hsub hy
    subst y
    exact K.down_closed hs (Finset.singleton_subset_iff.mpr hy) (Finset.singleton_nonempty x)

theorem augmentation_chain (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (x : E) (hspace : K.space = {x})
    (p : E → (Fin 1 → ℝ)) (hp : p x 0 = 1) :
    d 0 (chain (faces K hK 1) p) = wedge 0 (Fin.elim0 : Fin 0 → E) := by
  rw [faces_one_of_space_singleton K hK x hspace]
  simp only [chain,Finset.sum_singleton,basis_eq_wedge,map_smul,d_wedge]
  have hv : ∀ j, vertices (⟨{x},by simp⟩ : Set.powersetCard E 1) j = x := by
    intro j
    exact Finset.mem_singleton.mp (vertices_mem (⟨{x},by simp⟩ : Set.powersetCard E 1) j)
  have hd : Matrix.det (show Matrix (Fin 1) (Fin 1) ℝ from fun _ => p x) = 1 := by
    exact (Matrix.det_fin_one _).trans hp
  simp only [hv]
  change (Real.sign (Matrix.det (fun _ : Fin 1 => p x)) : ℂ) •
    (∑ i : Fin 1, (-1 : ℂ)^i.val • wedge 0 (fun _ : Fin 0 => x)) = _
  rw [hd]
  simp only [Real.sign_one,Complex.ofReal_one,one_smul,Fin.sum_univ_one,Fin.val_zero,pow_zero]
  congr 1
  exact Subsingleton.elim _ _

end Fundamental

/-! Alternating functions on vertex labels act on oriented exterior chains. -/

namespace ChainHomotopy

section

open scoped BigOperators

open Oriented

variable {Y : Type*}

variable [LinearOrder Y]

lemma Complex.coneLift_fills (K : Complex Y) {n : ℕ} (hn : n ≠ 0)
    (r : Degree Y n →ₗ[ℂ] Degree Y n)
    (hr : ∀ x ∈ K.chains n, Chains.boundary Y (r x : Chains.Algebra Y) = 0)
    {x : Degree Y n} (hx : x ∈ K.chains n) : d n (coneLift r x) = r x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    rw [coneLift_wedge]
    exact d_cone_cycle n _ (average_augmentation hn v) _ (hr _ (K.wedge_mem v hv))
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx => simp only [map_smul, hx]

lemma homotopy_equation (K : Complex Y)
    (F : ∀ n, Degree Y n →ₗ[ℂ] Degree Y n)
    (hF0 : F 0 = LinearMap.id)
    (hF : ∀ n x, x ∈ K.chains (n+1) → d n (F (n+1) x) = F n (d n x))
    (n : ℕ) {x : Degree Y (n+1)} (hx : x ∈ K.chains (n+1)) :
    d (n+1) (homotopy F (n+1) x) = F (n+1) x - x - homotopy F n (d n x) := by
  induction n with
  | zero =>
    apply K.coneLift_fills (by omega) _ ?_ hx
    intro y hy
    simp only [homotopy, LinearMap.zero_comp, LinearMap.sub_apply,
      LinearMap.id_apply, LinearMap.zero_apply, sub_zero]
    change Chains.boundary Y (F 1 y - y : Degree Y 1) = 0
    have he := hF 0 y hy
    rw [hF0] at he
    have hz : d 0 (F 1 y - y) = 0 := by simp only [map_sub, he, LinearMap.id_apply, sub_self]
    exact congrArg Subtype.val hz
  | succ n ih =>
    apply K.coneLift_fills (by omega) _ ?_ hx
    intro y hy
    have he := hF (n+1) y hy
    have hp := ih (K.d_mem (n+1) hy)
    have hz : d (n+1) (F (n+2) y - y - homotopy F (n+1) (d (n+1) y)) = 0 := by
      rw [map_sub, map_sub, he, hp, d_square, map_zero, sub_zero, sub_self]
    exact congrArg Subtype.val hz

end

section

open scoped BigOperators

open Oriented

variable {Y Z W : Type*}

lemma vertexMap_average (n : ℕ) (f : Y → Z) (v : Fin n → Y) :
    vertexMap f (average n v) = average n (f ∘ v) := by
  simp only [average, map_smul, map_sum, vertexMap_single, Function.comp_apply]

variable [LinearOrder Y]

lemma relabel_cone (n : ℕ) (f : Y → Z) (v : Y →₀ ℂ) (x : Degree Y n) :
    relabel (n+1) f (cone n v x) = cone n (vertexMap f v) (relabel n f x) := by
  apply Subtype.ext
  simp only [relabel_coe, cone_coe, map_mul, ExteriorAlgebra.map_apply_ι]

lemma coneLift_natural [LinearOrder Z] {n : ℕ}
    (r : Degree Y n →ₗ[ℂ] Degree Y n) (s : Degree Z n →ₗ[ℂ] Degree Z n)
    (f : Y → Z) (hf : ∀ x, relabel n f (r x) = s (relabel n f x)) (x : Degree Y n) :
    relabel (n+1) f (coneLift r x) = coneLift s (relabel n f x) := by
  have he : (relabel (n+1) f).comp (coneLift r) = (coneLift s).comp (relabel n f) := by
    apply linearMap_ext_wedge
    intro v
    simp only [LinearMap.comp_apply, coneLift_wedge, relabel_wedge,
      relabel_cone, vertexMap_average, hf]
  exact LinearMap.congr_fun he x

lemma homotopy_natural [LinearOrder Z]
    (F : ∀ n, Degree Y n →ₗ[ℂ] Degree Y n)
    (G : ∀ n, Degree Z n →ₗ[ℂ] Degree Z n) (f : Y → Z)
    (hf : ∀ n x, relabel n f (F n x) = G n (relabel n f x))
    (n : ℕ) (x : Degree Y n) :
    relabel (n+1) f (homotopy F n x) = homotopy G n (relabel n f x) := by
  induction n with
  | zero => simp only [homotopy, LinearMap.zero_apply, map_zero]
  | succ n ih =>
    apply coneLift_natural _ _ f ?_ x
    intro y
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      map_sub, hf, ih, d_relabel]

end

open scoped BigOperators

open Oriented

variable {Y H : Type*} [LinearOrder Y] [Monoid H] [MulAction H Y]

lemma coinvariant_cocycle_comparison (K : Complex Y) (hK : K.IsInvariant (H := H))
    (F : ∀ n, Degree Y n →ₗ[ℂ] Degree Y n)
    (hF0 : F 0 = LinearMap.id)
    (hF : ∀ n x, x ∈ K.chains (n+1) → d n (F (n+1) x) = F n (d n x))
    (hFeq : ∀ n (h : H) x,
      relabel n (fun y => h • y) (F n x) = F n (relabel n (fun y => h • y) x))
    (n : ℕ) (ψ : Degree Y (n+1) →ₗ[ℂ] ℂ)
    (hψ : ∀ (h : H) x, ψ (relabel (n+1) (fun y => h • y) x) = ψ x)
    (hψd : ∀ x, ψ (d (n+1) x) = 0)
    (c : K.chains (n+1))
    (hc : (⟨d n c, K.d_mem n c.property⟩ : K.chains n) ∈ K.relations hK n) :
    ψ (F (n+1) c) = ψ c := by
  let u : K.chains n →ₗ[ℂ] ℂ := (ψ.comp (homotopy F n)).comp (K.chains n).subtype
  have hu : ∀ x ∈ K.relations hK n, u x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨h, y⟩, rfl⟩ := hx
      change ψ (homotopy F n (relabel n (fun y => h • y) (y : Degree Y n) - (y : Degree Y n))) = 0
      rw [map_sub, map_sub,
        ← homotopy_natural F F (fun y => h • y) (fun i => hFeq i h), hψ, sub_self]
    | zero => exact map_zero u
    | add x y _ _ hx hy => simp only [map_add, hx, hy, add_zero]
    | smul a x _ hx => simp only [map_smul, hx, smul_zero]
  have hzero : ψ (homotopy F n (d n c)) = 0 :=
    hu ⟨d n c, K.d_mem n c.property⟩ hc
  have he := congrArg ψ (homotopy_equation K F hF0 hF n c.property)
  rw [hψd, map_sub, map_sub, hzero, sub_zero] at he
  exact sub_eq_zero.mp he.symm

end ChainHomotopy

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_BarycentricChains
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.Oriented.instCoeFunAltFunctionForallForallFin_2 _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace ChainHomotopy

open scoped BigOperators

open Oriented

variable {Y H : Type*} [LinearOrder Y]

open Classical in

lemma Complex.projection_wedge (K : Complex Y) (n : ℕ) (v : Fin n → Y) :
    (K.projection n (wedge n v) : Degree Y n) =
      if Finset.univ.image v ∈ K.faces then wedge n v else 0 := by
  classical
  rw [projection, AltFunction.lift_wedge]
  dsimp only [Complex.projectionValues]
  split_ifs <;> rfl

lemma Complex.projection_self (K : Complex Y) (n : ℕ) {x : Degree Y n}
    (hx : x ∈ K.chains n) : (K.projection n x : Degree Y n) = x := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    rw [K.projection_wedge, ite_eq_left hv]
  | zero => simp only [map_zero, Submodule.coe_zero]
  | add x y _ _ hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
  | smul a x _ hx => simp only [map_smul, Submodule.coe_smul, hx]

lemma Complex.chains_zero (K : Complex Y) : K.chains 0 = ⊤ := by
  apply top_unique
  rw [← span_wedges 0]
  apply Submodule.span_le.mpr
  rintro x ⟨v, rfl⟩
  apply K.wedge_mem
  simpa using K.empty_mem

variable [Group H] [MulAction H Y]

lemma Complex.image_mem_iff (K : Complex Y) (hK : K.IsInvariant (H := H))
    (h : H) (s : Finset Y) : s.image (fun y => h • y) ∈ K.faces ↔ s ∈ K.faces := by
  constructor
  · intro hs
    have he := hK h⁻¹ _ hs
    simpa only [Finset.image_image, Function.comp_def, inv_smul_smul, Finset.image_id'] using he
  · exact hK h s

lemma Complex.projection_relabel (K : Complex Y) (hK : K.IsInvariant (H := H))
    (n : ℕ) (h : H) (x : Degree Y n) :
    (K.projection n (relabel n (fun y => h • y) x) : Degree Y n) =
      relabel n (fun y => h • y) (K.projection n x : Degree Y n) := by
  classical
  have he : ((K.chains n).subtype.comp (K.projection n)).comp
      (relabel n (fun y => h • y)) =
      (relabel n (fun y => h • y)).comp ((K.chains n).subtype.comp (K.projection n)) := by
    apply linearMap_ext_wedge
    intro v
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, relabel_wedge,
      K.projection_wedge]
    have he : Finset.univ.image ((fun y => h • y) ∘ v) ∈ K.faces ↔
        Finset.univ.image v ∈ K.faces := by
      rw [← Finset.image_image]
      exact K.image_mem_iff hK h _
    by_cases hv : Finset.univ.image v ∈ K.faces
    · rw [ite_eq_left (he.mpr hv), ite_eq_left hv, relabel_wedge]
    · rw [ite_eq_right (mt he.mp hv), ite_eq_right hv, map_zero]
  exact LinearMap.congr_fun he x

lemma source_coinvariant_comparison (K : Complex Y) (hK : K.IsInvariant (H := H))
    (F : ∀ n, K.chains n →ₗ[ℂ] Degree Y n)
    (hF0 : ∀ x, F 0 x = x)
    (hF : ∀ n (x : K.chains (n+1)), d n (F (n+1) x) =
      F n ⟨d n x, K.d_mem n x.property⟩)
    (hFeq : ∀ n (h : H) (x : K.chains n),
      relabel n (fun y => h • y) (F n x) =
        F n ⟨relabel n (fun y => h • y) x, K.relabel_mem hK n h x.property⟩)
    (n : ℕ) (ψ : Degree Y (n+1) →ₗ[ℂ] ℂ)
    (hψ : ∀ (h : H) x, ψ (relabel (n+1) (fun y => h • y) x) = ψ x)
    (hψd : ∀ x, ψ (d (n+1) x) = 0)
    (c : K.chains (n+1))
    (hc : (⟨d n c, K.d_mem n c.property⟩ : K.chains n) ∈ K.relations hK n) :
    ψ (F (n+1) c) = ψ c := by
  let G : ∀ n, Degree Y n →ₗ[ℂ] Degree Y n := fun n => (F n).comp (K.projection n)
  have hG0 : G 0 = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change F 0 (K.projection 0 x) = x
    rw [hF0, K.projection_self 0]
    rw [K.chains_zero]
    trivial
  have hGK (n : ℕ) (x : K.chains n) : G n x = F n x := by
    apply congrArg (F n)
    apply Subtype.ext
    exact K.projection_self n x.property
  have hG (n : ℕ) (x : Degree Y (n+1)) (hx : x ∈ K.chains (n+1)) :
      d n (G (n+1) x) = G n (d n x) := by
    rw [hGK (n+1) ⟨x,hx⟩, hGK n ⟨d n x,K.d_mem n hx⟩]
    exact hF n ⟨x,hx⟩
  have hGeq (n : ℕ) (h : H) (x : Degree Y n) :
      relabel n (fun y => h • y) (G n x) = G n (relabel n (fun y => h • y) x) := by
    change relabel n (fun y => h • y) (F n (K.projection n x)) =
      F n (K.projection n (relabel n (fun y => h • y) x))
    rw [hFeq]
    apply congrArg (F n)
    apply Subtype.ext
    exact (K.projection_relabel hK n h x).symm
  have he := coinvariant_cocycle_comparison K hK G hG0 hG hGeq n ψ hψ hψd c hc
  rw [hGK] at he
  exact he

end ChainHomotopy

namespace BarycentricChains

open scoped BigOperators

open Oriented ChainHomotopy

variable {V Y : Type*} [LinearOrder V]

lemma boundary_degree_zero [LinearOrder Y] (x : Degree Y 0) :
    Chains.boundary Y (x : Chains.Algebra Y) = 0 := by
  have he : (Chains.boundary Y).comp (Degree Y 0).subtype = 0 := by
    apply linearMap_ext_wedge
    intro v
    simp [wedge,exteriorPower.ιMulti_apply_coe,Chains.boundary]
  exact LinearMap.congr_fun he x

lemma labelMap_chain [LinearOrder Y] (b : Finset V → Y →₀ ℂ)
    (hb : ∀ s : Finset V, s.Nonempty → Chains.augmentation Y (b s) = 1)
    (n : ℕ) (x : Degree V (n+1)) :
    d n (labelMap b (n+1) x) = labelMap b n (d n x) := by
  induction n with
  | zero =>
    have he : (d 0).comp (labelMap b 1) = (labelMap b 0).comp (d 0) := by
      apply linearMap_ext_wedge
      intro v
      simp only [LinearMap.comp_apply,labelMap_wedge_succ]
      exact d_cone_cycle 0 _ (hb _ (Finset.image_nonempty.mpr Finset.univ_nonempty)) _
        (boundary_degree_zero _)
    exact LinearMap.congr_fun he x
  | succ n ih =>
    have he : (d (n+1)).comp (labelMap b (n+2)) = (labelMap b (n+1)).comp (d (n+1)) := by
      apply linearMap_ext_wedge
      intro v
      simp only [LinearMap.comp_apply,labelMap_wedge_succ]
      apply d_cone_cycle
      · exact hb _ (Finset.image_nonempty.mpr Finset.univ_nonempty)
      · have hz : d n (labelMap b (n+1) (d (n+1) (wedge (n+2) v))) = 0 := by
          rw [ih,d_square,map_zero]
        exact congrArg Subtype.val hz
    exact LinearMap.congr_fun he x

end BarycentricChains

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_Coning
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BassTrace.Sparse.Cuts

open Set Finset

open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma vertexMean_map {F : Type*} [AddCommGroup F] [Module ℝ F]
    (f : E ≃ᵃ[ℝ] F) {s : Finset E} (hs : s.Nonempty) :
    vertexMean (s.map f.toEquiv.toEmbedding) = f (vertexMean s) := by
  rw [vertexMean_eq_centroid hs, vertexMean_eq_centroid hs.map, Finset.centroid_map]
  simp only [Finset.centroid_def]
  convert (s.map_affineCombination id (s.centroidWeights ℝ)
    (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs) f.toAffineMap).symm using 1 <;> rfl

end BassTrace.Sparse.Cuts

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_GeometricSubcomplexes
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

/-! Local finiteness passes to a simplexwise finite subdivision. -/

namespace Sparse.Cuts

/-! Geometric subcomplexes used by the compatible-cut lemma. A marked subset
is a union of closed simplices, not necessarily the full complex induced by
its old vertices. Keeping this distinction is essential for unions of levels. -/

section

open Set Finset

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma isMarked_empty (K : Geometry.SimplicialComplex ℝ E) : IsMarked K ∅ := by
  intro x hx
  exact hx.elim

end

open Set Finset

open scoped Classical

end Sparse.Cuts

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_MarkedSubdivisions
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse.Cuts

section

open Set Finset

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace PointFiltration

variable {K : Geometry.SimplicialComplex ℝ V} {n : ℕ} (Q : PointFiltration K n)

lemma zero_carrier (hK : ∀ F ∈ K.faces, F.card ≤ n+1) {i : ℕ} (hi : i ≤ n)
    {z : V} (hz : z ∈ Q.Z 0) :
    ∃ F ∈ (Q.T i).faces, convexHull ℝ (F : Set V) ⊆ Q.Z i ∧
      z ∈ convexHull ℝ (F : Set V) ∧ F.card = i+1 ∧
      (∀ E ∈ (Q.T i).faces, z ∈ convexHull ℝ (E : Set V) → F ⊆ E) ∧
      (∀ E ∈ (Q.T i).faces, z ∈ convexHull ℝ (E : Set V) →
        E.card = i+1 → E = F) := by
  have hzi := Q.subset (Nat.zero_le i) hi hz
  obtain ⟨F,hF,hzF,hmin⟩ := exists_smallest_carrier (Q.T i)
    ((Q.marked i hi).subset_space hzi)
  obtain ⟨E,hE,hzE,hEZ⟩ := Q.marked i hi z hzi
  have hFZ := (convexHull_mono (hmin E hE hzE)).trans hEZ
  have hb := Q.dimension_bound hK hi hF hFZ
  have hl := Q.card_lower_of_mem_zero hi hz hF hFZ hzF
  have hc : F.card = i+1 := by omega
  refine ⟨F,hF,hFZ,hzF,hc,hmin,?_⟩
  intro E hE hzE hcard
  exact (Finset.eq_of_subset_of_card_le (hmin E hE hzE) (by omega)).symm

end PointFiltration

end

open Set Finset

open scoped Classical Topology

end BassTrace.Sparse.Cuts

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_OrbitAreas
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse ENNReal Classical

variable {Y Z : Type*} [DecidableEq Y] [DecidableEq Z]

lemma finsuppRelabel_single (e : Y ≃ Z) (y : Y) :
    Finsupp.domLCongr (R := ℝ) e (Finsupp.single y (1 : ℝ)) = Finsupp.single (e y) 1 := by
  ext z
  change (Finsupp.single y (1 : ℝ)) (e.symm z) = (Finsupp.single (e y) 1) z
  simp only [Finsupp.single_apply]
  have hh : y=e.symm z ↔ e y=z := ⟨fun h => by rw [h,Equiv.apply_symm_apply],
    fun h => by rw [←h,Equiv.symm_apply_apply]⟩
  simp [hh]

lemma simplexVertices_relabel (e : Y ≃ Z) (s : Finset Y) :
    (simplexVertices (s.map e.toEmbedding) : Set (Z →₀ ℝ)) =
      Finsupp.domLCongr (R := ℝ) e '' (simplexVertices s : Set (Y →₀ ℝ)) := by
  simp only [simplexVertices,Finset.coe_image,Finset.coe_map,Set.image_image]
  congr 1
  funext y
  exact (finsuppRelabel_single e y).symm

end

open Finset Set

open scoped Pointwise Classical

end Sparse

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_FaceFiltration
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace Sparse.Cuts

open Set Finset

open scoped Classical

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma vertexMean_weight_sum {F : Finset E} (hF : F.Nonempty) :
    ∑ _x ∈ F, (F.card : ℝ)⁻¹ = 1 := by
  simp [ne_of_gt (Nat.cast_pos.mpr hF.card_pos : (0:ℝ)<F.card)]

lemma vertexMean_eq_sum (F : Finset E) :
    vertexMean F = ∑ x ∈ F, (F.card : ℝ)⁻¹ • x := by
  simp only [vertexMean,Finset.smul_sum]

lemma vertexMean_mem_marked_iff (K : Geometry.SimplicialComplex ℝ E)
    {Z : Set E} (hZ : IsMarked K Z) {F : Finset E} (hF : F ∈ K.faces) :
    vertexMean F ∈ Z ↔ convexHull ℝ (F : Set E) ⊆ Z := by
  constructor
  · intro hm
    obtain ⟨T,hT,hmt,hTZ⟩ := hZ _ hm
    rw [vertexMean_eq_sum] at hmt
    have hFT := simplex_contains_positivePoint K hF hT (fun _ => (F.card : ℝ)⁻¹)
      (fun _ _ => inv_pos.mpr (Nat.cast_pos.mpr (K.nonempty_of_mem_faces hF).card_pos))
      (vertexMean_weight_sum (K.nonempty_of_mem_faces hF)) hmt
    exact (convexHull_mono hFT).trans hTZ
  · exact fun hh => hh (vertexMean_mem_convexHull (K.nonempty_of_mem_faces hF))

lemma segment_vertexMean_avoids (K : Geometry.SimplicialComplex ℝ E)
    {Z : Set E} (hZ : IsMarked K Z) {F G : Finset E}
    (hF : F ∈ K.faces) (hG : G ∈ K.faces) (hFG : F ⊆ G)
    (hmF : vertexMean F ∉ Z) (hmG : vertexMean G ∉ Z) :
    Disjoint (segment ℝ (vertexMean F) (vertexMean G)) Z := by
  apply Set.disjoint_left.mpr
  rintro q ⟨a,b,ha,hb,hab,rfl⟩ hq
  by_cases hb0 : b=0
  · have ha1 : a=1 := by linarith
    simp only [ha1,hb0,one_smul,zero_smul,add_zero] at hq
    exact hmF hq
  have hbpos : 0<b := lt_of_le_of_ne hb (Ne.symm hb0)
  let u : E → ℝ := fun x => if x ∈ F then (F.card : ℝ)⁻¹ else 0
  let w : E → ℝ := fun x => a*u x + b*(G.card : ℝ)⁻¹
  have hu : ∑ x ∈ G, u x = 1 := by
    calc
      _ = ∑ x ∈ F, u x := (Finset.sum_subset hFG (fun x _ hx => by simp [u,hx])).symm
      _ = ∑ _x ∈ F, (F.card : ℝ)⁻¹ := Finset.sum_congr rfl (fun x hx => by simp [u,hx])
      _ = 1 := vertexMean_weight_sum (K.nonempty_of_mem_faces hF)
  have hvec : ∑ x ∈ G, u x • x = vertexMean F := by
    calc
      _ = ∑ x ∈ F, u x • x :=
        (Finset.sum_subset hFG (fun x _ hx => by simp [u,hx])).symm
      _ = ∑ x ∈ F, (F.card : ℝ)⁻¹ • x :=
        Finset.sum_congr rfl (fun x hx => by simp [u,hx])
      _ = _ := (vertexMean_eq_sum F).symm
  have hw : ∀ x ∈ G, 0 < w x := by
    intro x _
    have hux : 0 ≤ u x := by dsimp [u]; split_ifs <;> positivity
    exact add_pos_of_nonneg_of_pos (mul_nonneg ha hux)
      (mul_pos hbpos (inv_pos.mpr (Nat.cast_pos.mpr (K.nonempty_of_mem_faces hG).card_pos)))
  have hws : ∑ x ∈ G, w x = 1 := by
    simp only [w,Finset.sum_add_distrib,← Finset.mul_sum,hu,
      vertexMean_weight_sum (K.nonempty_of_mem_faces hG),mul_one]
    exact hab
  have heq : ∑ x ∈ G, w x • x = a • vertexMean F + b • vertexMean G := by
    simp only [w,add_smul,mul_smul,Finset.sum_add_distrib,← Finset.smul_sum,hvec,
      ← vertexMean_eq_sum]
  obtain ⟨T,hT,hqT,hTZ⟩ := hZ _ hq
  rw [← heq] at hqT
  have hGT := simplex_contains_positivePoint K hG hT w hw hws hqT
  exact hmG (hTZ (convexHull_mono hGT (vertexMean_mem_convexHull (K.nonempty_of_mem_faces hG))))

lemma vertexMean_components_eq (K : Geometry.SimplicialComplex ℝ E)
    {P Z : Set E} (hZ : IsMarked K Z) {F G : Finset E}
    (hF : F ∈ K.faces) (hG : G ∈ K.faces) (hFG : F ⊆ G)
    (hGP : convexHull ℝ (G : Set E) ⊆ P)
    (hmF : vertexMean F ∉ Z) (hmG : vertexMean G ∉ Z) :
    connectedComponentIn (P \ Z) (vertexMean F) =
      connectedComponentIn (P \ Z) (vertexMean G) := by
  have hsub : segment ℝ (vertexMean F) (vertexMean G) ⊆ P \ Z := by
    intro q hq
    refine ⟨?_,fun hqZ => Set.disjoint_left.mp (segment_vertexMean_avoids K hZ hF hG hFG hmF hmG) hq hqZ⟩
    exact hGP ((convex_convexHull ℝ (G : Set E)).segment_subset
      (convexHull_mono hFG (vertexMean_mem_convexHull (K.nonempty_of_mem_faces hF)))
      (vertexMean_mem_convexHull (K.nonempty_of_mem_faces hG)) hq)
  have hh := (convex_segment (vertexMean F) (vertexMean G)).isPreconnected.subset_connectedComponentIn
    (left_mem_segment ℝ _ _) hsub (right_mem_segment ℝ _ _)
  exact connectedComponentIn_eq hh

end

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {K : Geometry.SimplicialComplex ℝ V} {n : ℕ}

namespace PointFiltration

variable (Q : PointFiltration K n)

lemma final_marked (i : ℕ) (hi : i≤n) : IsMarked (Q.T 0) (Q.Z i) :=
  (Q.refines (Nat.zero_le i) hi).preserves_marked (Q.marked i hi)

lemma hull_mem_iff_level_le (F : Q.FinalFace) {i : ℕ} (hi : i≤n) :
    convexHull ℝ (F.val : Set V)⊆Q.Z i ↔ Q.faceLevel F ≤ i := by
  rw [← vertexMean_mem_marked_iff (Q.T 0) (Q.final_marked i hi) F.property]
  exact Q.mean_mem_iff_level_le F hi

lemma faceLevel_mono (F G : Q.FinalFace) (hFG : F.val⊆G.val) :
    Q.faceLevel F≤Q.faceLevel G := by
  apply (Q.hull_mem_iff_level_le F (Q.faceLevel_le G)).mp
  exact (convexHull_mono hFG).trans
    ((Q.hull_mem_iff_level_le G (Q.faceLevel_le G)).mpr le_rfl)

lemma faceComponent_eq_of_level_eq (F G : Q.FinalFace) (hFG : F.val⊆G.val)
    (hlevel : Q.faceLevel F=Q.faceLevel G) : Q.faceComponent F=Q.faceComponent G := by
  have hi := Q.faceLevel_le G
  have hz : IsMarked (Q.T 0) (Q.below (Q.faceLevel G)) := by
    unfold below
    split_ifs
    · exact isMarked_empty _
    · exact Q.final_marked _ (by omega)
  have hP : convexHull ℝ (G.val : Set V)⊆Q.Z (Q.faceLevel G) :=
    (Q.hull_mem_iff_level_le G hi).mpr le_rfl
  have hFZ : vertexMean F.val∉Q.below (Q.faceLevel G) :=
    hlevel ▸ (Q.mean_mem_stratum F).2
  exact (by
    unfold faceComponent
    rw [hlevel]
    exact vertexMean_components_eq (Q.T 0) hz F.property G.property hFG hP hFZ
      (Q.mean_mem_stratum G).2)

lemma final_face_card_le_level (hK : ∀ F∈K.faces,F.card≤n+1) (F : Q.FinalFace) :
    F.val.card≤Q.faceLevel F+1 := by
  obtain ⟨S,hS⟩ := Q.refines (Nat.zero_le (Q.faceLevel F)) (Q.faceLevel_le F)
  obtain ⟨T,hT,hTZ,hFT⟩ := S.carrier_marked (Q.marked _ (Q.faceLevel_le F))
    (hS.symm ▸ F.property)
    ((Q.hull_mem_iff_level_le F (Q.faceLevel_le F)).mpr le_rfl)
  have hc := (Q.T 0).indep F.property |>.card_le_card_of_subset_affineSpan
    ((subset_convexHull ℝ _).trans (hFT.trans (convexHull_subset_affineSpan _)))
  exact hc.trans (Q.dimension_bound hK (Q.faceLevel_le F) hT hTZ)

end PointFiltration

end Sparse.Cuts

namespace Sparse

open Set Finset

open scoped BassTrace.Sparse Classical

variable {Y : Type*}

variable {H X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

omit [Γ.LocallyFinite] in
lemma componentSupport_nonempty (x : X) (F : (Q.point x).FinalFace) :
    (supportVertices ((Q.point x).faceComponent F)).Nonempty := by
  let p := GraphGeometry.pointProbability K ⟨Cuts.vertexMean F.val,
    GraphGeometry.faceComponent_mem_space Γ hΓ Q x F ((Q.point x).mean_mem_component F)⟩
  have hp := p.coeff_support_nonempty
  obtain ⟨y,hy⟩ := hp
  refine ⟨y,Cuts.vertexMean F.val,(Q.point x).mean_mem_component F,?_⟩
  have he : p.coeff=Cuts.vertexMean F.val := GraphGeometry.pointProbability_coeff K _
  exact he ▸ hy

end Sparse

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_SupportGeometry
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace Sparse.OrbitForms

open Set Finset

open scoped BassTrace.Sparse Classical

variable {H Y : Type*} [Group H] [MulAction H Y]

variable {X : Type*} [TopologicalSpace X] [MulAction H X]

variable {K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)}

variable {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ} {n : ℕ}

variable (Q : SeparatingFiltration (H := H) (X := X) K ρ R n)

namespace SeparatingFiltration

lemma translateFace_mean (h : H) (x : X) (F : (Q.point x).FinalFace) :
    Cuts.vertexMean (Q.translateFace h x F).val=push h (Cuts.vertexMean F.val) :=
  Cuts.vertexMean_map (push h).toAffineEquiv
    (((Q.pair 0).T.val x).complex.nonempty_of_mem_faces F.property)

lemma push_mem_marked_iff (h : H) (x : X) (i : ℕ) (p : Y →₀ ℝ) :
    push h p∈(Q.point (h • x)).Z i ↔ p∈(Q.point x).Z i := by
  constructor
  · intro hp
    have hh := (Q.pair i).markedEquivariant h⁻¹ (h • x) (push h p) hp
    change p∈(Q.pair i).P.val x
    simpa only [push_inv_push,inv_smul_smul] using hh
  · exact (Q.pair i).markedEquivariant h x p

lemma translateFace_level (h : H) (x : X) (F : (Q.point x).FinalFace) :
    (Q.point (h • x)).faceLevel (Q.translateFace h x F)=(Q.point x).faceLevel F := by
  apply Nat.le_antisymm
  · apply ((Q.point (h • x)).mean_mem_iff_level_le _ ((Q.point x).faceLevel_le F)).mp
    rw [Q.translateFace_mean,Q.push_mem_marked_iff]
    exact (Q.point x).mean_mem_faceLevel F
  · apply ((Q.point x).mean_mem_iff_level_le F ((Q.point (h • x)).faceLevel_le _)).mp
    have hh := (Q.point (h • x)).mean_mem_faceLevel (Q.translateFace h x F)
    rwa [Q.translateFace_mean,Q.push_mem_marked_iff] at hh

lemma push_mem_stratum_iff (h : H) (x : X) (i : ℕ) (p : Y →₀ ℝ) :
    push h p∈(Q.point (h • x)).stratum i ↔ p∈(Q.point x).stratum i := by
  simp only [Cuts.PointFiltration.stratum,Cuts.PointFiltration.below,Set.mem_sdiff,
    Q.push_mem_marked_iff]
  split_ifs <;> simp only [Set.mem_empty_iff_false,Q.push_mem_marked_iff]

lemma stratum_image (h : H) (x : X) (i : ℕ) :
    push h '' (Q.point x).stratum i=(Q.point (h • x)).stratum i := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact (Q.push_mem_stratum_iff h x i q).mpr hq
  · intro hp
    refine ⟨push h⁻¹ p,?_,?_⟩
    · have hh := (Q.push_mem_stratum_iff h⁻¹ (h • x) i p).mpr hp
      simpa only [inv_smul_smul] using hh
    · rw [←push_mul,mul_inv_cancel,push_one]

lemma translateFace_component (h : H) (x : X) (F : (Q.point x).FinalFace) :
    (Q.point (h • x)).faceComponent (Q.translateFace h x F)=
      push h '' (Q.point x).faceComponent F := by
  unfold Cuts.PointFiltration.faceComponent
  rw [Q.translateFace_level,Q.translateFace_mean]
  rw [←Q.stratum_image h x ((Q.point x).faceLevel F)]
  exact ((pushHomeomorph h).image_connectedComponentIn
    ((Q.point x).mean_mem_stratum F)).symm

end SeparatingFiltration

end Sparse.OrbitForms

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_ZeroCarriers
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

/-! Canonical affine polyhedral cutting and coning in a real vector space, without
manifold or cross-simplex metric compatibility assumptions. -/

/-! Local finiteness passes to a simplexwise finite subdivision. -/

/-! Geometric subcomplexes used by the compatible-cut lemma. A marked subset
is a union of closed simplices, not necessarily the full complex induced by
its old vertices. Keeping this distinction is essential for unions of levels. -/

namespace BassTrace.Sparse.Cuts

open Set Finset

open scoped Classical

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {K : Geometry.SimplicialComplex ℝ V} {n : ℕ}

namespace PointFiltration

variable (Q : PointFiltration K n)

lemma face_in_zero_carrier (hK : ∀ F ∈ K.faces, F.card ≤ n+1)
    {i : ℕ} (hi : i ≤ n) {z : V} (hz : z ∈ Q.Z 0) :
    ∃ S ∈ (Q.T i).faces, S.card = i+1 ∧ ∀ F ∈ (Q.T 0).faces,
      F.card = i+1 → convexHull ℝ (F : Set V) ⊆ Q.Z i → z ∈ F →
      convexHull ℝ (F : Set V) ⊆ convexHull ℝ (S : Set V) := by
  obtain ⟨S,hS,_,_,hc,_,huniq⟩ := Q.zero_carrier hK hi hz
  refine ⟨S,hS,hc,?_⟩
  intro F hF hFc hFZ hzF
  obtain ⟨D,hD⟩ := Q.refines (Nat.zero_le i) hi
  obtain ⟨U,hU,hUZ,hFU⟩ := D.carrier_marked (Q.marked i hi) (hD.symm ▸ hF) hFZ
  have hu := Q.dimension_bound hK hi hU hUZ
  have hlu := (Q.T 0).indep hF |>.card_le_card_of_subset_affineSpan
    ((subset_convexHull ℝ _).trans (hFU.trans (convexHull_subset_affineSpan _)))
  have hcU : U.card = i+1 := by omega
  have he : U = S := huniq U hU (hFU (subset_convexHull ℝ _ hzF)) hcU
  exact he ▸ hFU

lemma flagged_cofaces_card_le_two (hK : ∀ F ∈ K.faces, F.card ≤ n+1)
    {i : ℕ} (hi : i < n) {z : V} (hz : z ∈ Q.Z 0) {F : Finset V}
    (hFc : F.card = i+1) (hzF : z ∈ F) (B : Finset (Finset V))
    (hB : ∀ E ∈ B, E ∈ (Q.T 0).faces ∧ E.card = i+2 ∧
      convexHull ℝ (E : Set V) ⊆ Q.Z (i+1) ∧ F ⊆ E) : B.card ≤ 2 := by
  obtain ⟨S,_,hSc,hS⟩ := Q.face_in_zero_carrier hK (show i+1 ≤ n by omega) hz
  apply BassTrace.Sparse.facet_coface_card_le_two (Q.T 0) (S := S) ⟨z,hzF⟩
  · omega
  · exact fun E hE => (hB E hE).1
  · intro E hE
    obtain ⟨_,hc,_,hFE⟩ := hB E hE
    exact ⟨hFE,by omega⟩
  · intro E hE
    obtain ⟨hE,hc,hEZ,hFE⟩ := hB E hE
    exact (subset_convexHull ℝ _).trans (hS E hE (by omega) hEZ (hFE hzF))

end PointFiltration

end

end BassTrace.Sparse.Cuts

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_FiniteAverages
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace BassTrace.FiniteAverage

open Set Finset MeasureTheory

open scoped Classical

noncomputable section

variable {X V W : Type*} [MeasurableSpace X]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

variable (μ : Measure X)

lemma average_const [IsProbabilityMeasure μ] (v : V) :
    average μ (SimpleFunc.const X v)=v := by
  let :=  algebraicNormedGroup V
  let :=  algebraicNormedSpace V
  rw [average,← SimpleFunc.integral_eq,SimpleFunc.integral_const]
  simp

lemma average_precomp {Z : Type*} [MeasurableSpace Z] (ν : Measure Z)
    (h : Z → X) (hh : MeasurePreserving h ν μ) (hs : Function.Surjective h)
    (f : SimpleFunc X V) :
    average ν (f.comp h hh.measurable)=average μ f := by
  have he : (f.comp h hh.measurable).range=f.range := by
    ext v
    simp only [SimpleFunc.mem_range,Set.mem_range]
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨h z,rfl⟩
    · rintro ⟨x,rfl⟩
      obtain ⟨z,rfl⟩ := hs x
      exact ⟨z,rfl⟩
  unfold average
  rw [he]
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  exact hh.measureReal_preimage (f.measurableSet_fiber v).nullMeasurableSet

variable [IsFiniteMeasure μ]

lemma average_complex_eq_integral (f : SimpleFunc X ℂ) :
    average μ f=∫x,f x∂μ := by
  rw [average,← SimpleFunc.integral_eq]
  exact f.integral_eq_integral f.integrable_of_isFiniteMeasure

lemma norm_average_le_integral_norm (f : SimpleFunc X ℂ) :
    ‖average μ f‖≤∫x,‖f x‖∂μ := by
  rw [average_complex_eq_integral]
  exact norm_integral_le_integral_norm _

end

end BassTrace.FiniteAverage

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_SubdivisionWeights
attribute [-instance] _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.Sparse

section

open Set Finset

open scoped BassTrace.Sparse Classical

variable {Y : Type*}

lemma uniformVector_sum (s : Finset Y) (hs : s.Nonempty) :
    (uniformVector s).sum (fun _ c=>c)=1 := by
  have hh : (Finsupp.linearCombination ℂ (fun _ : Y=>(1:ℂ))) (uniformVector s)=1 := by
    simp [uniformVector,Nat.ne_of_gt hs.card_pos]
  simpa only [Finsupp.linearCombination_apply,smul_eq_mul,mul_one] using hh

lemma uniformVector_nat (s : Finset Y) {Z : Type*} (e : Y ≃ Z) :
    uniformVector (s.map e.toEmbedding)=Finsupp.domLCongr (R := ℂ) e (uniformVector s) := by
  simp only [uniformVector,Finset.sum_map,Finset.card_map,map_sum]
  apply Finset.sum_congr rfl
  intro y _
  exact (Finsupp.domLCongr_single (R := ℂ) e y _).symm

lemma supportVertices_push {H : Type*} [Group H] [MulAction H Y]
    (h : H) (U : Set (Y →₀ ℝ)) :
    supportVertices (OrbitForms.push h '' U)= (fun y=>h • y) '' supportVertices U := by
  ext y
  constructor
  · rintro ⟨p,⟨q,hq,rfl⟩,hy⟩
    refine ⟨h⁻¹ • y,⟨q,hq,?_⟩,smul_inv_smul h y⟩
    simpa only [Finsupp.mem_support_iff,OrbitForms.push_apply] using hy
  · rintro ⟨z,⟨p,hp,hz⟩,rfl⟩
    refine ⟨OrbitForms.push h p,⟨p,hp,rfl⟩,?_⟩
    simpa only [Finsupp.mem_support_iff,OrbitForms.push_apply,inv_smul_smul] using hz

variable {H X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hn : 0<n) (hR : 0≤R)

lemma componentVertices_nonempty (x : X) (F : (Q.point x).FinalFace) :
    (componentVertices Γ hΓ Q hK hn hR x F).Nonempty := by
  obtain ⟨y,hy⟩ := componentSupport_nonempty Γ hΓ Q x F
  exact ⟨y,(mem_componentVertices Γ hΓ Q hK hn hR x F y).mpr hy⟩

lemma componentVertices_nat (h : H) (x : X) (F : (Q.point x).FinalFace) :
    componentVertices Γ hΓ Q hK hn hR (h • x) (Q.translateFace h x F)=
      (componentVertices Γ hΓ Q hK hn hR x F).map (MulAction.toPerm h).toEmbedding := by
  ext y
  simp only [mem_componentVertices,Finset.mem_map,Equiv.coe_toEmbedding,MulAction.toPerm_apply]
  rw [Q.translateFace_component,supportVertices_push]
  rfl

lemma componentWeight_sum (x : X) (F : (Q.point x).FinalFace) :
    (componentWeight Γ hΓ Q hK hn hR x F).sum (fun _ c=>c)=1 :=
  uniformVector_sum _ (componentVertices_nonempty Γ hΓ Q hK hn hR x F)

lemma componentWeight_nat (h : H) (x : X) (F : (Q.point x).FinalFace) :
    componentWeight Γ hΓ Q hK hn hR (h • x) (Q.translateFace h x F)=
      Finsupp.domLCongr (R := ℂ) (MulAction.toPerm h) (componentWeight Γ hΓ Q hK hn hR x F) := by
  unfold componentWeight
  rw [componentVertices_nat,uniformVector_nat]

end

open Set Finset

open scoped BassTrace.Sparse Classical

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)

lemma faceWeight_sum (x : X) (F : Finset (Y →₀ ℝ)) :
    (faceWeight Γ hΓ Q hK hn hR y₀ x F).sum (fun _ c=>c)=1 := by
  unfold faceWeight
  split_ifs
  · exact componentWeight_sum Γ hΓ Q hK hn hR x _
  · simp

lemma faceWeight_face (x : X) (F : (Q.point x).FinalFace) :
    faceWeight Γ hΓ Q hK hn hR y₀ x F.val=componentWeight Γ hΓ Q hK hn hR x F := by
  unfold faceWeight
  have hf : F.val∈((Q.pair 0).T.val x).complex.faces := F.property
  rw [dite_eq_left hf]
  rfl

lemma faceWeight_nat (h : H) (x : X) (F : (Q.point x).FinalFace) :
    faceWeight Γ hΓ Q hK hn hR y₀ (h • x) (F.val.map (OrbitForms.push h).toEmbedding)=
      Finsupp.domLCongr (R := ℂ) (MulAction.toPerm h)
        (faceWeight Γ hΓ Q hK hn hR y₀ x F.val) := by
  change faceWeight Γ hΓ Q hK hn hR y₀ (h • x) (Q.translateFace h x F).val=_
  rw [faceWeight_face,faceWeight_face,componentWeight_nat]

lemma faceWeight_nested_equal_level (x : X) (F G : (Q.point x).FinalFace)
    (hFG : F.val⊆G.val) (hlevel : (Q.point x).faceLevel F=(Q.point x).faceLevel G) :
    faceWeight Γ hΓ Q hK hn hR y₀ x F.val=faceWeight Γ hΓ Q hK hn hR y₀ x G.val := by
  rw [faceWeight_face,faceWeight_face]
  exact componentWeight_eq_of_component Γ hΓ Q hK hn hR x x F G
    ((Q.point x).faceComponent_eq_of_level_eq F G hFG hlevel)

end BassTrace.Sparse

namespace BassTrace.SubdivisionChains

section

open Set Finset

open scoped BassTrace.Sparse Classical

open Sparse Oriented ChainHomotopy Fundamental OrientedIncidence

variable {Y : Type*} [LinearOrder Y] [LinearOrder (Y →₀ ℝ)]

variable {K : PreAbstractSimplicialComplex Y}

variable (T : Cuts.Subdivision (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))

omit [LinearOrder (Y →₀ ℝ)] in
lemma chart_vertex {k : ℕ} (v : Fin k → Y) (hv : Function.Injective v) (j : Fin k) :
    chart v (Finsupp.single (v j) 1)=Pi.single j 1 := by
  ext i
  simp [chart_apply,Finsupp.single_apply,Pi.single_apply,hv.eq_iff,eq_comm]

omit [LinearOrder (Y →₀ ℝ)] in
lemma localTriangulation_space (s : Finset Y) (hs : s∈K.faces) :
    (localTriangulation T s).space=convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)) := by
  rw [localTriangulation,Cuts.restrictComplex_space_of_respects _ _
    (T.respects (simplexVertices s) ⟨s,hs,rfl⟩),T.space_eq]
  exact Set.inter_eq_right.mpr
    ((Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).convexHull_subset_space ⟨s,hs,rfl⟩)

end

open Set Finset

open scoped BassTrace.Sparse Classical

open Sparse Oriented ChainHomotopy Fundamental OrientedIncidence

variable {Y : Type*} [LinearOrder Y] [LinearOrder (Y →₀ ℝ)]

variable {K : PreAbstractSimplicialComplex Y}

variable (T : Cuts.Subdivision (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))

omit [LinearOrder (Y →₀ ℝ)] in
lemma simplexVertices_image {k : ℕ} (v : Fin k → Y) :
    (simplexVertices (Finset.univ.image v) : Set (Y →₀ ℝ))=
      Set.range (fun i=>Finsupp.single (v i) (1:ℝ)) := by
  ext p
  simp only [simplexVertices,Finset.coe_image,Finset.coe_univ,Set.image_univ,Set.mem_image,
    Set.mem_range]
  constructor
  · rintro ⟨y,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨v i,⟨i,rfl⟩,rfl⟩

omit [LinearOrder (Y →₀ ℝ)] in
lemma localTriangulation_face {k : ℕ} (v : Fin (k+1) → Y)
    (hv : Function.Injective v) (i : Fin (k+1)) :
    Sparse.restrictComplex (localTriangulation T (Finset.univ.image v))
      {p | chart v p i=0}=
    localTriangulation T (Finset.univ.image (fun j=>v (i.succAbove j))) := by
  apply Geometry.SimplicialComplex.ext
  ext s
  change (s∈T.complex.faces ∧ (s : Set (Y →₀ ℝ))⊆
      convexHull ℝ (simplexVertices (Finset.univ.image v) : Set (Y →₀ ℝ))) ∧
      (s : Set (Y →₀ ℝ))⊆{p | chart v p i=0} ↔ s∈T.complex.faces ∧
      (s : Set (Y →₀ ℝ))⊆convexHull ℝ
        (simplexVertices (Finset.univ.image (fun j=>v (i.succAbove j))) : Set (Y →₀ ℝ))
  rw [simplexVertices_image,simplexVertices_image]
  rw [← parent_face_chart (fun j=>Finsupp.single (v j) (1:ℝ)) (chart v)
    (chart_vertex v hv) i,Set.subset_inter_iff]
  tauto

lemma subdivision_chain_wedge (k : ℕ) (v : Fin (k+1) → Y)
    (hs : Finset.univ.image v∈K.faces) :
    d k (subdivision T (k+1) (wedge (k+1) v))=
      subdivision T k (d k (wedge (k+1) v)) := by
  by_cases hv : Function.Injective v
  swap
  · rw [wedge_eq_zero_of_not_injective _ hv,map_zero,map_zero,map_zero,map_zero]
  cases k with
  | zero =>
    rw [subdivision_wedge_face T 0 v hs]
    have hsp : (localTriangulation T (Finset.univ.image v)).space=
        {Finsupp.single (v 0) (1:ℝ)} := by
      rw [localTriangulation_space T _ hs,simplexVertices_image]
      have he : Set.range (fun i : Fin 1=>Finsupp.single (v i) (1:ℝ))=
          {Finsupp.single (v 0) (1:ℝ)} := by simp
      rw [he,convexHull_singleton]
    rw [augmentation_chain _ _ _ hsp _ (by
      simpa only [Pi.single_eq_same] using congrFun (chart_vertex v hv 0) 0)]
    change wedge 0 (Fin.elim0 : Fin 0 → (Y →₀ ℝ))=
      relabel 0 (fun y : Y=>Finsupp.single y (1:ℝ)) (d 0 (wedge 1 v))
    rw [d_wedge]
    change _=relabel 0 _ (∑i : Fin 1,(-1:ℂ)^i.val •
      wedge 0 (fun j=>v (i.succAbove j)))
    rw [Fin.sum_univ_one]
    simp only [Fin.val_zero,pow_zero,one_smul,relabel_wedge]
    congr 1
    exact Subsingleton.elim _ _
  | succ k =>
    rw [subdivision_wedge_face T (k+1) v hs]
    let w : Fin (k+2) ↪ (Y →₀ ℝ) := ⟨fun i=>Finsupp.single (v i) 1,
      (Finsupp.single_left_injective (by norm_num : (1:ℝ)≠0)).comp hv⟩
    have hw : Set.range w=(simplexVertices (Finset.univ.image v) : Set (Y →₀ ℝ)) :=
      (simplexVertices_image v).symm
    rw [boundary_chain_restrictions _ _ _ w hw (localTriangulation_space T _ hs)
      (chart v) (chart_vertex v hv),d_wedge,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    congr 1
    have hsub : Finset.univ.image (fun j=>v (i.succAbove j))⊆Finset.univ.image v := by
      intro y hy
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image.mpr ⟨i.succAbove j,Finset.mem_univ _,rfl⟩
    have hface := (K.isRelLowerSet_faces hs).2 hsub
      (Finset.image_nonempty.mpr Finset.univ_nonempty)
    rw [subdivision_wedge_face T k _ hface]
    congr 2
    exact localTriangulation_face T v hv i

end BassTrace.SubdivisionChains

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_SparseChains
attribute [-instance] _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.BarycentricChains

open scoped BigOperators

open Oriented ChainHomotopy

variable {V W Y Z : Type*} [LinearOrder V] [LinearOrder W] [LinearOrder Y]

lemma labelMap_natural_local (b : Finset V → Y →₀ ℂ) (c : Finset W → Z →₀ ℂ)
    (f : V → W) (g : Y → Z) (s : Finset V)
    (hbc : ∀ t : Finset V,t⊆s → t.Nonempty → c (t.image f)=vertexMap g (b t))
    (n : ℕ) (v : Fin n → V) (hv : ∀i,v i∈s) :
    relabel n g (labelMap b n (wedge n v))=
      labelMap c n (wedge n (f ∘ v)) := by
  induction n with
  | zero =>
    simp only [labelMap_wedge_zero,relabel_wedge]
    congr 1
    exact funext fun i=>Fin.elim0 i
  | succ n ih =>
    rw [labelMap_wedge_recursion,labelMap_wedge_recursion,map_sum]
    have him : Finset.univ.image v⊆s := by
      intro y hy
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hy
      exact hv i
    have hh := hbc _ him (Finset.image_nonempty.mpr Finset.univ_nonempty)
    rw [← Finset.image_image,hh]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul,relabel_cone,ih (fun j=>v (i.succAbove j)) (fun j=>hv (i.succAbove j))]
    rfl

end BassTrace.BarycentricChains

namespace BassTrace.Sparse

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical

open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains

variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)

lemma sparseChainFamily_chain_face (x : X) (k : ℕ) (v : Fin (k+1) → Y)
    (hs : Finset.univ.image v∈K.faces) :
    d k (sparseChainFamily Γ hΓ Q hK hn hR y₀ x (k+1) (wedge (k+1) v))=
      sparseChainFamily Γ hΓ Q hK hn hR y₀ x k (d k (wedge (k+1) v)) := by
  unfold sparseChainFamily
  simp only [LinearMap.comp_apply]
  rw [labelMap_chain _ (fun s _=>by
    simpa only [Chains.augmentation,Finsupp.linearCombination_apply,smul_eq_mul,mul_one]
      using faceWeight_sum Γ hΓ Q hK hn hR y₀ x s),
    subdivision_chain_wedge _ k v hs]

lemma sparseChainFamily_chain (x : X) (k : ℕ) (c : Degree Y (k+1))
    (hc : c∈(augmentedComplex K).chains (k+1)) :
    d k (sparseChainFamily Γ hΓ Q hK hn hR y₀ x (k+1) c)=
      sparseChainFamily Γ hΓ Q hK hn hR y₀ x k (d k c) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨v,hv,rfl⟩ := hc
    have hv' : Finset.univ.image v∈K.faces := by
      rcases hv with hv | hv
      · exact False.elim ((Finset.image_nonempty.mpr Finset.univ_nonempty).ne_empty hv)
      · exact hv
    exact sparseChainFamily_chain_face Γ hΓ Q hK hn hR y₀ x k v hv'
  | zero => simp
  | add c e _ _ hc he => simp only [map_add,hc,he]
  | smul a c _ hc => simp only [map_smul,hc]

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_AveragedChains
attribute [-instance] _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.SubdivisionChains

open Set Finset

open scoped BassTrace.Sparse Classical

open Sparse Oriented ChainHomotopy Fundamental OrientedIncidence Sparse.OrbitForms

variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y}

variable (P : MarkedPair (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))

omit [LinearOrder (Y →₀ ℝ)] in
lemma originalHull_push (h : H) (s : Finset Y) :
    convexHull ℝ (simplexVertices (s.map (MulAction.toPerm h).toEmbedding) : Set (Y →₀ ℝ))=
      push h '' convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)) := by
  rw [simplexVertices_relabel]
  exact ((push h).toLinearMap.image_convexHull _).symm

omit [LinearOrder (Y →₀ ℝ)] in
lemma localFace_push (h : H) (x : X) (s : Finset Y) (F : Finset (Y →₀ ℝ))
    (hF : F∈(localTriangulation (P.T.val x) s).faces) :
    F.map (push h).toEmbedding∈
      (localTriangulation (P.T.val (h • x)) (s.map (MulAction.toPerm h).toEmbedding)).faces := by
  refine ⟨P.equivariant h x F hF.1,?_⟩
  rw [originalHull_push]
  intro p hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
  exact ⟨q,hF.2 hq,rfl⟩

omit [LinearOrder Y] [LinearOrder (Y →₀ ℝ)] in
lemma map_push_inverse (h : H) (F : Finset (Y →₀ ℝ)) :
    (F.map (push h).toEmbedding).map (push h⁻¹).toEmbedding=F := by
  rw [Finset.map_map]
  have he : (push h).toEmbedding.trans (push h⁻¹).toEmbedding=Function.Embedding.refl (Y →₀ ℝ) :=
    Function.Embedding.ext (push_inv_push (Y := Y) h)
  rw [he,Finset.map_refl]

omit [LinearOrder Y] [LinearOrder (Y →₀ ℝ)] in
lemma map_action_inverse (h : H) (s : Finset Y) :
    (s.map (MulAction.toPerm h).toEmbedding).map (MulAction.toPerm h⁻¹).toEmbedding=s := by
  rw [Finset.map_map]
  have he : (MulAction.toPerm h).toEmbedding.trans (MulAction.toPerm h⁻¹).toEmbedding=
      Function.Embedding.refl Y := Function.Embedding.ext (fun y : Y => inv_smul_smul h y)
  rw [he,Finset.map_refl]

omit [LinearOrder (Y →₀ ℝ)] in
lemma local_faces_natural (h : H) (x : X) (s : Finset Y) (hs : s∈K.faces)
    (ht : s.map (MulAction.toPerm h).toEmbedding∈K.faces) (k : ℕ) :
    (faces (localTriangulation (P.T.val x) s) (localTriangulation_finite _ _ hs) k).map
      (simplexMap (push h).toEmbedding k)=
    faces (localTriangulation (P.T.val (h • x)) (s.map (MulAction.toPerm h).toEmbedding))
      (localTriangulation_finite _ _ ht) k := by
  ext F
  rw [Finset.mem_map,mem_faces]
  constructor
  · rintro ⟨E,hE,rfl⟩
    exact localFace_push P h x s E.val ((mem_faces _ _ _ E).mp hE)
  · intro hF
    refine ⟨⟨F.val.map (push h⁻¹).toEmbedding,by simp⟩,?_,?_⟩
    · rw [mem_faces]
      have hh := localFace_push P h⁻¹ (h • x) (s.map (MulAction.toPerm h).toEmbedding)
        F.val hF
      simpa only [map_action_inverse,inv_smul_smul] using hh
    · apply Subtype.ext
      change (F.val.map (push h⁻¹).toEmbedding).map (push h).toEmbedding=F.val
      simpa only [inv_inv] using map_push_inverse (Y := Y) h⁻¹ F.val

lemma subdivision_natural_face (h : H) (x : X) (k : ℕ) (v : Fin (k+1) → Y)
    (hs : Finset.univ.image v∈K.faces)
    (ht : (Finset.univ.image v).map (MulAction.toPerm h).toEmbedding∈K.faces) :
    relabel (k+1) (push h) (subdivision (P.T.val x) (k+1) (wedge (k+1) v))=
      subdivision (P.T.val (h • x)) (k+1) (wedge (k+1) (fun i=>h • v i)) := by
  have himage : Finset.univ.image (fun i=>h • v i)=
      (Finset.univ.image v).map (MulAction.toPerm h).toEmbedding := by
    simp only [Finset.map_eq_image,Finset.image_image,Function.comp_def,
      Equiv.coe_toEmbedding,MulAction.toPerm_apply]
  have htv : Finset.univ.image (fun i=>h • v i)∈K.faces := himage.symm ▸ ht
  rw [subdivision_wedge_face _ _ _ hs,subdivision_wedge_face _ _ _ htv]
  calc
    _ = chain ((faces (localTriangulation (P.T.val x) (Finset.univ.image v))
        (localTriangulation_finite _ _ hs) (k+1)).map (simplexMap (push h).toEmbedding (k+1)))
        (chart (fun i=>h • v i)) := by
      exact chain_relabel _ _ (chart (fun i=>h • v i)) (push h).toEmbedding (by
        intro p
        ext i
        change (push h p) (h • v i) = p (v i)
        rw [push_apply,inv_smul_smul])
    _ = _ := by
      congr 1
      simpa only [himage] using local_faces_natural P h x (Finset.univ.image v) hs ht (k+1)

end BassTrace.SubdivisionChains

namespace BassTrace.Sparse

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical

open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains

variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)

omit [LinearOrder (Y →₀ ℝ)] [LinearOrder Y] in
lemma vertexMap_perm (h : H) (b : Y →₀ ℂ) :
    vertexMap (fun y=>h • y) b=Finsupp.domLCongr (R := ℂ) (MulAction.toPerm h) b := by
  ext y
  change Finsupp.mapDomain (MulAction.toPerm h) b y = _
  rw [Finsupp.mapDomain_equiv_apply]
  rfl

lemma sparseChainFamily_natural_face (h : H) (x : X) (k : ℕ) (v : Fin (k+1) → Y)
    (hs : Finset.univ.image v∈K.faces)
    (ht : (Finset.univ.image v).map (MulAction.toPerm h).toEmbedding∈K.faces) :
    relabel (k+1) (fun y=>h • y)
        (sparseChainFamily Γ hΓ Q hK hn hR y₀ x (k+1) (wedge (k+1) v))=
      sparseChainFamily Γ hΓ Q hK hn hR y₀ (h • x) (k+1)
        (wedge (k+1) (fun i=>h • v i)) := by
  unfold sparseChainFamily
  simp only [LinearMap.comp_apply]
  rw [←subdivision_natural_face (Q.pair 0) h x k v hs ht,subdivision_wedge_face _ _ _ hs]
  simp only [chain,map_sum]
  apply Finset.sum_congr rfl
  intro F hF
  simp only [map_smul,basis_eq_wedge,relabel_wedge]
  congr 1
  apply labelMap_natural_local _ _ _ _ F.val
  · intro t htF htn
    have htf : t∈((Q.pair 0).T.val x).complex.faces :=
      ((Q.pair 0).T.val x).complex.down_closed
        ((mem_faces _ _ _ F).mp hF).1 htF htn
    rw [vertexMap_perm]
    calc
      _ = faceWeight Γ hΓ Q hK hn hR y₀ (h • x)
          (t.map (OrbitForms.push h).toEmbedding) := by
        apply congrArg (faceWeight Γ hΓ Q hK hn hR y₀ (h • x))
        ext p
        simp only [Finset.mem_image,Finset.mem_map]
        rfl
      _ = _ := faceWeight_nat Γ hΓ Q hK hn hR y₀ h x ⟨t,htf⟩
  · exact fun i=>OrientedIncidence.vertices_mem F i

lemma sparseChainFamily_natural
    (hInv : (augmentedComplex K).IsInvariant (H := H))
    (h : H) (x : X) (k : ℕ) (c : Degree Y k)
    (hc : c∈(augmentedComplex K).chains k) :
    relabel k (fun y=>h • y) (sparseChainFamily Γ hΓ Q hK hn hR y₀ x k c)=
      sparseChainFamily Γ hΓ Q hK hn hR y₀ (h • x) k (relabel k (fun y=>h • y) c) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨v,hv,rfl⟩:=hc
    cases k with
    | zero => rw [sparseChainFamily_zero,sparseChainFamily_zero]; rfl
    | succ k =>
      have hs : Finset.univ.image v∈K.faces := by
        rcases hv with hv | hv
        · exact False.elim ((Finset.image_nonempty.mpr Finset.univ_nonempty).ne_empty hv)
        · exact hv
      rw [relabel_wedge]
      apply sparseChainFamily_natural_face Γ hΓ Q hK hn hR y₀ h x k v hs
      have ht := hInv h (Finset.univ.image v) (Set.mem_insert_of_mem ∅ hs)
      rcases ht with ht | ht
      · exact False.elim ((Finset.image_nonempty.mpr (Finset.image_nonempty.mpr
          Finset.univ_nonempty)).ne_empty ht)
      · convert ht using 1
        all_goals try with_reducible_and_instances rfl
        ext y
        simp only [Finset.mem_image,Finset.mem_map]
        rfl
  | zero => simp
  | add c d _ _ hc hd => simp only [map_add,hc,hd]
  | smul a c _ hc => simp only [map_smul,hc]

end BassTrace.Sparse

namespace BassTrace.FiniteAverage

open Set Finset MeasureTheory

open scoped Classical

variable {X V W Z : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Z] [Module ℂ Z]

variable (μ : Measure X) [IsFiniteMeasure μ]

lemma locallyConstantLinearMap_post (F : X → V →ₗ[ℂ] W)
    (hF : ∀v,IsLocallyConstant (fun x=>F x v)) (L : W →ₗ[ℂ] Z) (v : V) :
    L (locallyConstantLinearMap μ F hF v)=
      average μ ((ofLocallyConstant (fun x=>F x v) (hF v)).map L) :=
  (average_map μ (L.restrictScalars ℝ) _).symm

lemma locallyConstantLinearMap_const [IsProbabilityMeasure μ] (F : V →ₗ[ℂ] W) (v : V) :
    locallyConstantLinearMap μ (fun _=>F) (fun v=>IsLocallyConstant.const (F v)) v=F v := by
  change average μ (ofLocallyConstant _ _)=F v
  have he : ofLocallyConstant (fun _ : X=>F v) (IsLocallyConstant.const (F v)) =
      SimpleFunc.const X (F v) := by ext; rfl
  rw [he,average_const]

end BassTrace.FiniteAverage

namespace BassTrace.Sparse

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical

open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains FiniteAverage

variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]
  [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)

variable (μ : Measure X) [IsProbabilityMeasure μ]

lemma averagedSparseChain_zero (c : Degree Y 0) :
    averagedSparseChain Γ hΓ Q hK hn hR y₀ μ 0 c=c := by
  unfold averagedSparseChain
  simp_rw [sparseChainFamily_zero]
  exact locallyConstantLinearMap_const μ LinearMap.id c

lemma averagedSparseChain_chain (k : ℕ) (c : Degree Y (k+1))
    (hc : c∈(augmentedComplex K).chains (k+1)) :
    d k (averagedSparseChain Γ hΓ Q hK hn hR y₀ μ (k+1) c)=
      averagedSparseChain Γ hΓ Q hK hn hR y₀ μ k (d k c) := by
  unfold averagedSparseChain
  rw [locallyConstantLinearMap_post]
  apply congrArg (FiniteAverage.average μ)
  apply SimpleFunc.ext
  intro x
  exact sparseChainFamily_chain Γ hΓ Q hK hn hR y₀ x k c hc

lemma averagedSparseChain_natural
    (hInv : (augmentedComplex K).IsInvariant (H := H))
    (hμ : ∀h : H,MeasurePreserving (fun x : X=>h • x) μ μ)
    (h : H) (k : ℕ) (c : Degree Y k) (hc : c∈(augmentedComplex K).chains k) :
    relabel k (fun y=>h • y) (averagedSparseChain Γ hΓ Q hK hn hR y₀ μ k c)=
      averagedSparseChain Γ hΓ Q hK hn hR y₀ μ k (relabel k (fun y=>h • y) c) := by
  unfold averagedSparseChain
  rw [locallyConstantLinearMap_post]
  let f := ofLocallyConstant
    (fun x=>sparseChainFamily Γ hΓ Q hK hn hR y₀ x k (relabel k (fun y=>h • y) c))
    (sparseChainFamily_local Γ hΓ Q hK hn hR y₀ k _)
  change FiniteAverage.average μ _=FiniteAverage.average μ f
  rw [←average_precomp μ μ (fun x : X=>h • x) (hμ h)
    (MulAction.bijective h).surjective f]
  apply congrArg (FiniteAverage.average μ)
  apply SimpleFunc.ext
  intro x
  exact sparseChainFamily_natural Γ hΓ Q hK hn hR y₀ hInv h x k c hc

lemma averagedSparseChain_comparison
    (hInv : (augmentedComplex K).IsInvariant (H := H))
    (hμ : ∀h : H,MeasurePreserving (fun x : X=>h • x) μ μ)
    (k : ℕ) (ψ : Degree Y (k+1) →ₗ[ℂ] ℂ)
    (hψ : ∀(h : H) c,ψ (relabel (k+1) (fun y=>h • y) c)=ψ c)
    (hψd : ∀c,ψ (d (k+1) c)=0)
    (c : (augmentedComplex K).chains (k+1))
    (hc : (⟨d k c,(augmentedComplex K).d_mem k c.property⟩ :
      (augmentedComplex K).chains k)∈(augmentedComplex K).relations hInv k) :
    ψ (averagedSparseChain Γ hΓ Q hK hn hR y₀ μ (k+1) c)=ψ c := by
  refine source_coinvariant_comparison (augmentedComplex K) hInv
    (fun k=>(averagedSparseChain Γ hΓ Q hK hn hR y₀ μ k).comp
      ((augmentedComplex K).chains k).subtype)
    (fun c=>averagedSparseChain_zero Γ hΓ Q hK hn hR y₀ μ c)
    (fun k c=>averagedSparseChain_chain Γ hΓ Q hK hn hR y₀ μ k c c.property)
    (fun k h c=>averagedSparseChain_natural Γ hΓ Q hK hn hR y₀ μ hInv hμ h k c c.property)
    k ψ hψ hψd c hc

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_BarycentricBounds
attribute [-instance] _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.BarycentricChains

section

open Set Finset

open scoped Classical

open Oriented ChainHomotopy OrientedIncidence

variable {V Y : Type*} [LinearOrder V]

lemma cone_square (k : ℕ) (b : Y →₀ ℂ) (c : Degree Y k) :
    cone (k+1) b (cone k b c)=0 := by
  apply Subtype.ext
  change ExteriorAlgebra.ι ℂ b * (ExteriorAlgebra.ι ℂ b * (c : Chains.Algebra Y))=0
  rw [←mul_assoc,ExteriorAlgebra.ι_sq_zero,zero_mul]

lemma vertices_image {k : ℕ} (s : Set.powersetCard V k) :
    Finset.univ.image (vertices s)=s.val := by
  apply Finset.coe_injective
  simpa only [Finset.coe_image,Finset.coe_univ,Set.image_univ] using vertices_range s

lemma labelMap_basis_recursion (b : Finset V → Y →₀ ℂ) (k : ℕ)
    (s : Set.powersetCard V (k+1)) :
    labelMap b (k+1) (basis (k+1) s)=
      cone k (b s.val) (∑i : Fin (k+1),(-1:ℂ)^i.val • labelMap b k (basis k (eraseFace s i))) := by
  rw [basis_eq_wedge,labelMap_wedge_succ,vertices_image,←basis_eq_wedge,
    boundary_basis,map_sum]
  simp only [map_smul]

lemma labelMap_eq_filtered (b : Finset V → Y →₀ ℂ) (ℓ : Finset V → ℕ)
    (P : Set (Finset V))
    (hP : ∀s∈P,∀t⊆s,t.Nonempty→t∈P)
    (hcard : ∀s∈P,s.card≤ℓ s+1)
    (hmono : ∀s∈P,∀t∈P,t⊆s→ℓ t≤ℓ s)
    (heq : ∀s∈P,∀t∈P,t⊆s→ℓ t=ℓ s→b t=b s)
    (k : ℕ) (s : Set.powersetCard V (k+1)) (hs : s.val∈P) (hℓ : ℓ s.val=k) :
    labelMap b (k+1) (basis (k+1) s)=filteredLabel b ℓ k s := by
  induction k with
  | zero => simp only [filteredLabel,hℓ,ite_true, if_true]
  | succ k ih =>
    rw [filteredLabel,ite_eq_left hℓ,labelMap_basis_recursion,map_sum,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul,map_smul]
    congr 1
    have hsub : (eraseFace s i).val⊆s.val := Finset.erase_subset _ _
    have hE : (eraseFace s i).val∈P := hP s.val hs _ hsub
      (Finset.card_pos.mp (by rw [(eraseFace s i).property]; omega))
    have hlow := hcard _ hE
    rw [(eraseFace s i).property] at hlow
    have hhigh := hmono s.val hs _ hE hsub
    rw [hℓ] at hhigh
    by_cases he : ℓ (eraseFace s i).val=k
    · rw [ih (eraseFace s i) hE he]
    · have he' : ℓ (eraseFace s i).val=k+1 := by omega
      have hb := heq s.val hs _ hE hsub (he'.trans hℓ.symm)
      rw [labelMap_basis_recursion,hb,cone_square]
      cases k <;> simp only [filteredLabel,ite_eq_right he,map_zero]

end

section

open Set Finset

open scoped Classical

open Oriented ChainHomotopy OrientedIncidence

variable {V : Type*} [LinearOrder V]

lemma eraseFace_injective {k : ℕ} (s : Set.powersetCard V (k+1)) :
    Function.Injective (eraseFace s) := by
  intro i j he
  apply (vertices s).injective
  exact (Finset.erase_inj s.val (vertices_mem s i)).mp (congrArg Subtype.val he)

lemma filteredCount_eq_zero (ℓ : Finset V → ℕ) (k : ℕ)
    (s : Set.powersetCard V (k+1)) (hs : ℓ s.val≠k) : filteredCount ℓ k s=0 := by
  cases k <;> simp only [filteredCount,ite_eq_right hs]

lemma filteredCount_pos_level (ℓ : Finset V → ℕ) (k : ℕ)
    (s : Set.powersetCard V (k+1)) (hs : 0<filteredCount ℓ k s) : ℓ s.val=k := by
  by_contra h
  rw [filteredCount_eq_zero ℓ k s h] at hs
  exact Nat.lt_irrefl 0 hs

lemma sum_facets_fiberwise (k : ℕ) (A : Finset (Set.powersetCard V (k+2)))
    (B : Finset (Set.powersetCard V (k+1)))
    (hAB : ∀s∈A,∀i,eraseFace s i∈B) (w : Set.powersetCard V (k+1) → ℕ) :
    ∑s∈A,∑i : Fin (k+2),w (eraseFace s i)=
      ∑t∈B,(incidencePairs A t).card*w t := by
  rw [←Finset.sum_product A Finset.univ (fun p=>w (eraseFace p.1 p.2))]
  symm
  calc
    _ = ∑t∈B,∑p∈incidencePairs A t,w (eraseFace p.1 p.2) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [←Finset.sum_const_nat (s := incidencePairs A t)
        (f := fun p=>w (eraseFace p.1 p.2)) (fun p hp=>congrArg w (Finset.mem_filter.mp hp).2)]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun p hp=>hAB p.1 (Finset.mem_product.mp hp).1 p.2) _

lemma incidencePairs_card_le (k : ℕ) (A : Finset (Set.powersetCard V (k+2)))
    (t : Set.powersetCard V (k+1)) :
    (incidencePairs A t).card≤(A.filter (fun s=>t.val⊆s.val)).card := by
  apply Finset.card_le_card_of_injOn (fun p=>p.1)
  · intro p hp
    obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hp).1,?_⟩
    rw [←he]
    exact Finset.erase_subset _ _
  · intro p hp q hq he
    apply Prod.ext he
    obtain ⟨_,hp⟩ := Finset.mem_filter.mp hp
    obtain ⟨_,hq⟩ := Finset.mem_filter.mp hq
    apply eraseFace_injective q.1
    simpa only [he] using hp.trans hq.symm

lemma filteredCount_sum_step (ℓ : Finset V → ℕ) (k : ℕ)
    (A : Finset (Set.powersetCard V (k+2))) (B : Finset (Set.powersetCard V (k+1)))
    (hAB : ∀s∈A,∀i,eraseFace s i∈B)
    (hbranch : ∀t∈B,0<filteredCount ℓ k t →
      ((A.filter (fun s=>ℓ s.val=k+1)).filter (fun s=>t.val⊆s.val)).card≤2) :
    ∑s∈A,filteredCount ℓ (k+1) s≤2*∑t∈B,filteredCount ℓ k t := by
  have he : (∑s∈A,filteredCount ℓ (k+1) s)=
      ∑s∈A.filter (fun s=>ℓ s.val=k+1),∑i : Fin (k+2),filteredCount ℓ k (eraseFace s i) := by
    simp only [filteredCount,Finset.sum_filter]
  rw [he,sum_facets_fiberwise k _ B (fun s hs=>hAB s (Finset.mem_filter.mp hs).1),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  by_cases hw : 0<filteredCount ℓ k t
  · exact Nat.mul_le_mul_right _ ((incidencePairs_card_le k _ t).trans (hbranch t ht hw))
  · have hz : filteredCount ℓ k t=0 := by omega
    simp only [hz,mul_zero,le_refl]

end

section

open Set Finset

open scoped Classical

open OrientedIncidence Fundamental Sparse

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [LinearOrder V]

variable {K : Geometry.SimplicialComplex ℝ V} {n : ℕ}

namespace ActualFlags

variable (Q : Cuts.PointFiltration K n)

omit [LinearOrder V] in
lemma level_face (s : Finset V) (hs : s∈(Q.T 0).faces) :
    level Q s=Q.faceLevel ⟨s,hs⟩ := dite_eq_left hs

lemma count_pos_zero (k : ℕ) (s : Set.powersetCard V (k+1))
    (hs : s.val∈(Q.T 0).faces) (hp : 0<filteredCount (level Q) k s) :
    ∃z∈s.val,z∈Q.Z 0 := by
  induction k with
  | zero =>
    obtain ⟨z,hz⟩ := Finset.card_eq_one.mp s.property
    have hl := filteredCount_pos_level (level Q) 0 s hp
    rw [level_face Q s.val hs] at hl
    have hm := Q.mean_mem_faceLevel ⟨s.val,hs⟩
    rw [hl,hz] at hm
    simp only [Cuts.vertexMean,Finset.card_singleton,Nat.cast_one,inv_one,Finset.sum_singleton,one_smul] at hm
    exact ⟨z,hz.symm ▸ Finset.mem_singleton_self z,hm⟩
  | succ k ih =>
    rw [filteredCount] at hp
    split_ifs at hp with hl
    · obtain ⟨i,_,hi⟩ := Finset.sum_pos_iff.mp hp
      have hE : (eraseFace s i).val∈(Q.T 0).faces :=
        (Q.T 0).down_closed hs (Finset.erase_subset _ _)
          (Finset.card_pos.mp (by rw [(eraseFace s i).property]; omega))
      obtain ⟨z,hz,hZ⟩ := ih (eraseFace s i) hE hi
      exact ⟨z,Finset.erase_subset _ _ hz,hZ⟩
    · omega

lemma localFaces_erase (L : Geometry.SimplicialComplex ℝ V) (hL : L.faces.Finite)
    (k : ℕ) (s : Set.powersetCard V (k+2)) (hs : s∈faces L hL (k+2)) (i : Fin (k+2)) :
    eraseFace s i∈faces L hL (k+1) := by
  rw [mem_faces] at hs ⊢
  exact L.down_closed hs (Finset.erase_subset _ _)
    (Finset.card_pos.mp (by rw [(eraseFace s i).property]; omega))

lemma count_sum_step (hK : ∀s∈K.faces,s.card≤n+1)
    (L : Geometry.SimplicialComplex ℝ V) (hL : L.faces.Finite)
    (hLT : L.faces⊆(Q.T 0).faces) (k : ℕ) (hk : k<n) :
    ∑s∈faces L hL (k+2),filteredCount (level Q) (k+1) s≤
      2*∑t∈faces L hL (k+1),filteredCount (level Q) k t := by
  apply filteredCount_sum_step (level Q) k _ _ (localFaces_erase L hL k)
  intro t ht hp
  obtain ⟨z,hzt,hz⟩ := count_pos_zero Q k t (hLT ((mem_faces L hL _ t).mp ht)) hp
  let B := ((faces L hL (k+2)).filter (fun s=>level Q s.val=k+1)).filter (fun s=>t.val⊆s.val)
  have hh : (B.image Subtype.val).card≤2 := by
    apply Q.flagged_cofaces_card_le_two hK hk hz t.property hzt
    intro E hE
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hE
    obtain ⟨hs,hsub⟩ := Finset.mem_filter.mp hs
    obtain ⟨hs,hl⟩ := Finset.mem_filter.mp hs
    have hsf := hLT ((mem_faces L hL _ s).mp hs)
    refine ⟨hsf,s.property,?_,hsub⟩
    rw [level_face Q s.val hsf] at hl
    exact (Q.hull_mem_iff_level_le ⟨s.val,hsf⟩ (show k+1≤n by omega)).mpr hl.le
  simpa only [Finset.card_image_of_injective _ Subtype.val_injective] using hh

lemma count_sum_bound (hK : ∀s∈K.faces,s.card≤n+1)
    (L : Geometry.SimplicialComplex ℝ V) (hL : L.faces.Finite)
    (hLT : L.faces⊆(Q.T 0).faces) (k : ℕ) (hk : k≤n) :
    ∑s∈faces L hL (k+1),filteredCount (level Q) k s≤
      2^k * ((faces L hL 1).filter (fun s=>level Q s.val=0)).card := by
  induction k with
  | zero => simp [filteredCount]
  | succ k ih =>
    calc
      _ ≤ 2*∑s∈faces L hL (k+1),filteredCount (level Q) k s :=
        count_sum_step Q hK L hL hLT k (by omega)
      _ ≤ 2*(2^k * _) := Nat.mul_le_mul_left 2 (ih (by omega))
      _ = _ := by rw [pow_succ]; ac_rfl

end ActualFlags

end

section

open Set Finset

open scoped Classical

open Oriented ChainHomotopy OrientedIncidence Sparse

variable {V Y : Type*} [LinearOrder V]

lemma cone_single_wedge (k : ℕ) (y : Y) (v : Fin k → Y) :
    cone k (Finsupp.single y 1) (wedge k v)=wedge (k+1) (Fin.cons y v) := by
  apply Subtype.ext
  simp only [cone_coe,wedge,exteriorPower.ιMulti_apply_coe,ExteriorAlgebra.ιMulti_succ_apply,
    Fin.cons_zero,Matrix.vecTail,Function.comp_def,Fin.cons_succ]

lemma cone_uniform_wedge (k : ℕ) (s : Finset Y) (v : Fin k → Y) :
    cone k (uniformVector s) (wedge k v)=
      ∑y∈s,(s.card : ℂ)⁻¹ • wedge (k+1) (Fin.cons y v) := by
  change coneLeft k (wedge k v) (uniformVector s)=_
  rw [uniformVector,map_sum]
  apply Finset.sum_congr rfl
  intro y _
  have he : Finsupp.single y (s.card : ℂ)⁻¹=(s.card : ℂ)⁻¹ • Finsupp.single y 1 := by simp
  rw [he,map_smul]
  exact congrArg ((s.card : ℂ)⁻¹ • ·) (cone_single_wedge k y v)

lemma norm_uniform_cone_wedge (k : ℕ) (W s : Finset Y) (hs : s.Nonempty) (hsW : s⊆W)
    (ψ : Degree Y (k+1) →ₗ[ℂ] ℂ) (M : ℝ)
    (hM : ∀v : Fin (k+1) → Y,(∀i,v i∈W)→‖ψ (wedge (k+1) v)‖≤M)
    (v : Fin k → Y) (hv : ∀i,v i∈W) :
    ‖ψ (cone k (uniformVector s) (wedge k v))‖≤M := by
  rw [cone_uniform_wedge,map_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑_y∈s,(s.card : ℝ)⁻¹*M := by
      apply Finset.sum_le_sum
      intro y hy
      rw [map_smul,norm_smul,norm_inv,Complex.norm_natCast]
      apply mul_le_mul_of_nonneg_left (hM (Fin.cons y v) ?_) (inv_nonneg.mpr (Nat.cast_nonneg _))
      intro i
      exact Fin.cases (hsW hy) hv i
    _ = M := by
      rw [Finset.sum_const, nsmul_eq_mul, ←mul_assoc, mul_inv_cancel₀,one_mul]
      exact_mod_cast hs.card_pos.ne'

lemma filteredLabel_norm (b : Finset V → Y →₀ ℂ) (ℓ : Finset V → ℕ)
    (P : Set (Finset V)) (hP : ∀s∈P,∀t⊆s,t.Nonempty→t∈P)
    (W : Finset Y)
    (hb : ∀s∈P,∃t : Finset Y,t.Nonempty ∧ t⊆W ∧ b s=uniformVector t)
    (M : ℝ) (_hM0 : 0≤M)
    (k : ℕ) (s : Set.powersetCard V (k+1)) (hs : s.val∈P)
    (ψ : Degree Y (k+1) →ₗ[ℂ] ℂ)
    (hM : ∀v : Fin (k+1) → Y,(∀i,v i∈W)→‖ψ (wedge (k+1) v)‖≤M) :
    ‖ψ (filteredLabel b ℓ k s)‖≤M*(filteredCount ℓ k s : ℝ) := by
  induction k with
  | zero =>
    rw [filteredLabel,filteredCount]
    split_ifs with he
    · obtain ⟨t,ht,htW,hsb⟩:=hb s.val hs
      rw [labelMap_basis_recursion,Fin.sum_univ_one]
      simp only [Fin.val_zero,pow_zero,one_smul]
      rw [basis_eq_wedge,
        labelMap_wedge_zero,hsb,Nat.cast_one,mul_one]
      exact norm_uniform_cone_wedge 0 W t ht htW ψ M hM _ (fun i=>Fin.elim0 i)
    · simp only [map_zero,norm_zero,Nat.cast_zero,mul_zero,le_refl]
  | succ k ih =>
    rw [filteredLabel,filteredCount]
    split_ifs with he
    · obtain ⟨t,ht,htW,hsb⟩:=hb s.val hs
      rw [map_sum,map_sum,Nat.cast_sum,Finset.mul_sum]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul,map_smul,norm_smul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
      apply ih (eraseFace s i)
        (hP s.val hs _ (Finset.erase_subset _ _)
          (Finset.card_pos.mp (by rw [(eraseFace s i).property]; omega)))
        (ψ.comp (cone (k+1) (b s.val)))
      intro v hv
      change ‖ψ (cone (k+1) (b s.val) (wedge (k+1) v))‖≤M
      rw [hsb]
      exact norm_uniform_cone_wedge (k+1) W t ht htW ψ M hM v hv
    · simpa only [map_zero,norm_zero,Nat.cast_zero,mul_zero] using (le_refl (0:ℝ))

end

open Set Finset

open scoped Classical

open Oriented ChainHomotopy OrientedIncidence Sparse Fundamental

variable {V Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [LinearOrder V]

variable {K : Geometry.SimplicialComplex ℝ V} {n : ℕ}

lemma norm_sign_complex_le (r : ℝ) : ‖(Real.sign r : ℂ)‖≤1 := by
  rcases Real.sign_apply_eq r with h|h|h <;> simp [h]

lemma labeled_chain_bound (Q : Cuts.PointFiltration K n)
    (hK : ∀s∈K.faces,s.card≤n+1)
    (L : Geometry.SimplicialComplex ℝ V) (hL : L.faces.Finite)
    (hLT : L.faces⊆(Q.T 0).faces)
    (b : Finset V → Y →₀ ℂ)
    (heq : ∀s∈L.faces,∀t∈L.faces,t⊆s→
      ActualFlags.level Q t=ActualFlags.level Q s→b t=b s)
    (W : Finset Y) (hb : ∀s∈L.faces,∃t : Finset Y,t.Nonempty ∧ t⊆W ∧ b s=uniformVector t)
    (p : V → (Fin (n+1) → ℝ))
    (ψ : Degree Y (n+1) →ₗ[ℂ] ℂ) (M : ℝ) (hM0 : 0≤M)
    (hM : ∀v : Fin (n+1) → Y,(∀i,v i∈W)→‖ψ (wedge (n+1) v)‖≤M) :
    ‖ψ (labelMap b (n+1) (chain (faces L hL (n+1)) p))‖≤
      M*(2^n * ((faces L hL 1).filter (fun s=>ActualFlags.level Q s.val=0)).card : ℕ) := by
  have hcard s (hs : s∈L.faces) : s.card≤ActualFlags.level Q s+1 := by
    rw [ActualFlags.level_face Q s (hLT hs)]
    exact Q.final_face_card_le_level hK ⟨s,hLT hs⟩
  have hmono s (hs : s∈L.faces) t (ht : t∈L.faces) (hts : t⊆s) :
      ActualFlags.level Q t≤ActualFlags.level Q s := by
    rw [ActualFlags.level_face Q t (hLT ht),ActualFlags.level_face Q s (hLT hs)]
    exact Q.faceLevel_mono ⟨t,hLT ht⟩ ⟨s,hLT hs⟩ hts
  calc
    _ ≤ ∑s∈faces L hL (n+1),‖ψ ((labelMap b (n+1))
        ((Real.sign (Matrix.det (fun i=>p (vertices s i))) : ℂ) • basis (n+1) s))‖ := by
      rw [chain,map_sum,map_sum]
      exact norm_sum_le _ _
    _ ≤ ∑s∈faces L hL (n+1),M*(filteredCount (ActualFlags.level Q) n s : ℝ) := by
      apply Finset.sum_le_sum
      intro s hs
      have hsf := (mem_faces L hL _ s).mp hs
      have hl : ActualFlags.level Q s.val=n := by
        have hlow := hcard s.val hsf
        rw [s.property] at hlow
        have hhigh := Q.faceLevel_le ⟨s.val,hLT hsf⟩
        rw [←ActualFlags.level_face Q s.val (hLT hsf)] at hhigh
        omega
      rw [map_smul,map_smul,norm_smul]
      apply (mul_le_of_le_one_left (norm_nonneg _) (norm_sign_complex_le _)).trans
      rw [labelMap_eq_filtered b (ActualFlags.level Q) L.faces
        (fun s hs t hts ht=>L.down_closed hs hts ht) hcard hmono heq n s hsf hl]
      exact filteredLabel_norm b (ActualFlags.level Q) L.faces
        (fun s hs t hts ht=>L.down_closed hs hts ht) W hb M hM0 n s hsf ψ hM
    _ = M*((∑s∈faces L hL (n+1),filteredCount (ActualFlags.level Q) n s : ℕ):ℝ) := by
      rw [Nat.cast_sum,Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by exact_mod_cast ActualFlags.count_sum_bound Q hK L hL hLT n le_rfl) hM0

end BassTrace.BarycentricChains

namespace BassTrace.BarycentricChains.ActualFlags

open Set Finset MeasureTheory

open scoped Classical

open Sparse Fundamental

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {K : Geometry.SimplicialComplex ℝ V} {n : ℕ}

lemma singleton_mean (s : Set.powersetCard V 1) : s.val={Cuts.vertexMean s.val} := by
  obtain ⟨z,hz⟩ := Finset.card_eq_one.mp s.property
  simp only [hz,Cuts.vertexMean,Finset.card_singleton,Nat.cast_one,inv_one,Finset.sum_singleton,one_smul]

lemma zeroFaces_card_le (Q : Cuts.PointFiltration K n)
    (L : Geometry.SimplicialComplex ℝ V) (hL : L.faces.Finite)
    (hLT : L.faces⊆(Q.T 0).faces) (S : Set V) (hLS : L.space⊆S)
    (hfin : (Q.Z 0∩S).Finite) :
    ((faces L hL 1).filter (fun s=>level Q s.val=0)).card≤hfin.toFinset.card := by
  apply Finset.card_le_card_of_injOn (fun s=>Cuts.vertexMean s.val)
  · intro s hs
    obtain ⟨hs,hl⟩ := Finset.mem_filter.mp hs
    have hsf := (mem_faces L hL _ s).mp hs
    change Cuts.vertexMean s.val∈hfin.toFinset
    rw [Set.Finite.mem_toFinset]
    refine ⟨?_,hLS (L.convexHull_subset_space hsf
      (Cuts.vertexMean_mem_convexHull (L.nonempty_of_mem_faces hsf)))⟩
    rw [level_face Q s.val (hLT hsf)] at hl
    exact hl ▸ Q.mean_mem_faceLevel ⟨s.val,hLT hsf⟩
  · intro s _ t _ he
    apply Subtype.ext
    dsimp only at he
    rw [singleton_mean s,singleton_mean t,he]

lemma zeroFaces_real_le_count [MeasurableSpace V] [MeasurableSingletonClass V]
    (Q : Cuts.PointFiltration K n)
    (L : Geometry.SimplicialComplex ℝ V) (hL : L.faces.Finite)
    (hLT : L.faces⊆(Q.T 0).faces) (S : Set V) (hLS : L.space⊆S)
    (hfin : (Q.Z 0∩S).Finite) :
    (((faces L hL 1).filter (fun s=>level Q s.val=0)).card : ℝ)≤
      (Measure.count (Q.Z 0∩S)).toReal := by
  rw [Measure.count_apply_finite _ hfin,ENNReal.toReal_natCast]
  exact_mod_cast zeroFaces_card_le Q L hL hLT S hLS hfin

end BassTrace.BarycentricChains.ActualFlags

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_SparseBounds
attribute [-instance] _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.Sparse

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical

open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains

variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)

attribute [local instance] OAI.BassTrace.Sparse.instMeasurableSpaceFinsuppReal_solutions_1
local instance instBorelSpaceFinsuppReal_solutions_1 : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩

lemma sparseChainFamily_bound (x : X) (v : Fin (n+1) → Y)
    (hs : Finset.univ.image v∈K.faces) (hv : Function.Injective v)
    (ψ : Degree Y (n+1) →ₗ[ℂ] ℂ) (M : ℝ) (hM0 : 0≤M)
    (hM : ∀w : Fin (n+1) → Y,(∀i,w i∈GraphGeometry.labelWindow Γ n R (Finset.univ.image v))→
      ‖ψ (wedge (n+1) w)‖≤M) :
    ‖ψ (sparseChainFamily Γ hΓ Q hK hn hR y₀ x (n+1) (wedge (n+1) v))‖≤
      M*(2^n : ℕ)*(Measure.count ((Q.pair 0).P.val x∩
        convexHull ℝ (simplexVertices (Finset.univ.image v) : Set (Y →₀ ℝ)))).toReal := by
  let s := Finset.univ.image v
  let L := localTriangulation ((Q.pair 0).T.val x) s
  have hfin : L.faces.Finite := localTriangulation_finite ((Q.pair 0).T.val x) s hs
  have hLT : L.faces⊆((Q.point x).T 0).faces := fun _ h=>h.1
  have hd : ∀s∈K.faces,s.card≤n+1 := by
    intro s hs
    obtain ⟨t,_,hst,hc,_⟩ := hK s hs
    exact (Finset.card_le_card hst).trans_eq hc
  have hdim : ∀s∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces,s.card≤n+1 := by
    rintro _ ⟨s,hs,rfl⟩
    exact Finset.card_image_le.trans (hd s hs)
  have hLspace := localTriangulation_space ((Q.pair 0).T.val x) s hs
  have hsc : s.card=n+1 := by rw [Finset.card_image_of_injective _ hv,Finset.card_univ,Fintype.card_fin]
  have hzero := zero_inter_simplex_finite Q hd ⟨s,hs,hsc⟩ x
  have hbound := labeled_chain_bound (Q.point x) hdim L hfin hLT
    (faceWeight Γ hΓ Q hK hn hR y₀ x) (fun s hs t ht hts he=>by
      rw [ActualFlags.level_face (Q.point x) t (hLT ht),
        ActualFlags.level_face (Q.point x) s (hLT hs)] at he
      exact faceWeight_nested_equal_level Γ hΓ Q hK hn hR y₀ x
        ⟨t,hLT ht⟩ ⟨s,hLT hs⟩ hts he)
    (GraphGeometry.labelWindow Γ n R s) (fun F hF=>by
      refine ⟨componentVertices Γ hΓ Q hK hn hR x ⟨F,hLT hF⟩,
        componentVertices_nonempty Γ hΓ Q hK hn hR x _,?_,?_⟩
      · intro y hy
        exact componentSupport_subset Γ hΓ Q hK hn hR x ⟨F,hLT hF⟩ s
          ((convexHull_min hF.2 (convex_convexHull ℝ _))
            (Cuts.vertexMean_mem_convexHull (L.nonempty_of_mem_faces hF)))
          ((mem_componentVertices Γ hΓ Q hK hn hR x _ y).mp hy)
      · exact faceWeight_face Γ hΓ Q hK hn hR y₀ x ⟨F,hLT hF⟩)
    (chart v) ψ M hM0 hM
  change ‖ψ (labelMap _ (n+1) (subdivision _ (n+1) (wedge (n+1) v)))‖≤_
  rw [subdivision_wedge_succ,tupleSubdivision,dite_eq_left hs]
  apply hbound.trans
  rw [Nat.cast_mul,←mul_assoc]
  apply mul_le_mul_of_nonneg_left
    (ActualFlags.zeroFaces_real_le_count (Q.point x) L hfin hLT _ hLspace.subset hzero)
    (mul_nonneg hM0 (Nat.cast_nonneg _))

end

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical

open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains

variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]
  [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)

variable (μ : Measure X) [IsProbabilityMeasure μ]

attribute [local instance] OAI.BassTrace.Sparse.instMeasurableSpaceFinsuppReal_solutions_2
local instance instBorelSpaceFinsuppReal_solutions_2_rfb72ff_1 : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩
lemma averagedSparseChain_bound (v : Fin (n+1) → Y)
    (hs : Finset.univ.image v∈K.faces) (hv : Function.Injective v)
    (ψ : Degree Y (n+1) →ₗ[ℂ] ℂ) (M : ℝ) (hM0 : 0≤M)
    (hM : ∀w : Fin (n+1) → Y,(∀i,w i∈GraphGeometry.labelWindow Γ n R (Finset.univ.image v))→
      ‖ψ (wedge (n+1) w)‖≤M) :
    ‖ψ (averagedSparseChain Γ hΓ Q hK hn hR y₀ μ (n+1) (wedge (n+1) v))‖≤
      M*(2^n : ℕ)*(∫x,(Measure.count ((Q.pair 0).P.val x∩
        convexHull ℝ (simplexVertices (Finset.univ.image v) : Set (Y →₀ ℝ)))).toReal ∂μ) := by
  unfold averagedSparseChain
  rw [FiniteAverage.locallyConstantLinearMap_post]
  apply (FiniteAverage.norm_average_le_integral_norm μ _).trans
  have hZ : IsLocallyConstant (fun x=>(Measure.count ((Q.pair 0).P.val x∩
      convexHull ℝ (simplexVertices (Finset.univ.image v) : Set (Y →₀ ℝ)))).toReal) :=
    ((Q.pair 0).P.localConstancy_inter (simplexVertices (Finset.univ.image v))
      ⟨_,hs,rfl⟩ _ subset_rfl).comp (fun A=>(Measure.count A).toReal)
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_mono
  · exact SimpleFunc.integrable_of_isFiniteMeasure _ |>.norm
  · exact (FiniteAverage.ofLocallyConstant _ hZ).integrable_of_isFiniteMeasure.const_mul _
  · intro x
    exact sparseChainFamily_bound Γ hΓ Q hK hn hR y₀ x v hs hv ψ M hM0 hM

end BassTrace.Sparse

namespace BassTrace.BarycentricChains

open Set Finset

open scoped Classical

open Oriented ChainHomotopy

lemma finite_norm_bound {I : Type*} [Finite I] (f : I → ℂ) :
    ∃M : ℝ,0≤M ∧ ∀i,‖f i‖≤M := by
  let _ := Fintype.ofFinite I
  refine ⟨∑i,‖f i‖,Finset.sum_nonneg (fun _ _=>norm_nonneg _),?_⟩
  intro i
  exact Finset.single_le_sum (fun _ _=>norm_nonneg _) (Finset.mem_univ i)

lemma exists_finite_wedge_bound {Y : Type*} (k : ℕ) (W : Finset Y)
    (ψ : Degree Y k →ₗ[ℂ] ℂ) :
    ∃M : ℝ,0≤M ∧ ∀v : Fin k → Y,(∀i,v i∈W)→‖ψ (wedge k v)‖≤M := by
  let f : (Fin k → {y // y∈W}) → ℂ := fun v=>ψ (wedge k (fun i=>(v i).val))
  obtain ⟨M,hM,h⟩ := finite_norm_bound f
  refine ⟨M,hM,?_⟩
  intro v hv
  exact h (fun i=>⟨v i,hv i⟩)

end BassTrace.BarycentricChains

namespace BassTrace.Sparse

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical

open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains GraphGeometry

variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]
  [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)

variable (μ : Measure X) [IsProbabilityMeasure μ]

attribute [local instance] OAI.BassTrace.Sparse.instMeasurableSpaceFinsuppReal_solutions_3
local instance instBorelSpaceFinsuppReal_solutions_3_rfb72ff_1 : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩
lemma exists_chain_bound (C : SourceTop K n → ℝ) (hC : ∀σ,0≤C σ)
    (ψ : Degree Y (n+1) →ₗ[ℂ] ℂ) (c : Degree Y (n+1))
    (hc : c∈(augmentedComplex K).chains (n+1)) :
    ∃B : ℝ,0≤B ∧ ∀ε : ℝ,0<ε →
      ∀Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
        (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
        (realizationDistance Γ hΓ K n) R n,
      (∀σ : SourceTop K n,(∫x,(Measure.count ((Q.pair 0).P.val x∩
        convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))).toReal ∂μ)≤C σ*ε) →
      ‖ψ (averagedSparseChain Γ hΓ Q hK hn hR y₀ μ (n+1) c)‖≤B*ε := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨v,hv,rfl⟩ := hc
    by_cases hinj : Function.Injective v
    · have hs : Finset.univ.image v∈K.faces := by
        rcases hv with hv|hv
        · exact False.elim ((Finset.image_nonempty.mpr Finset.univ_nonempty).ne_empty hv)
        · exact hv
      have hsc : (Finset.univ.image v).card=n+1 := by
        rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_fin]
      let σ : SourceTop K n := ⟨Finset.univ.image v,hs,hsc⟩
      obtain ⟨M,hM0,hM⟩ := exists_finite_wedge_bound (n+1) (labelWindow Γ n R σ.val) ψ
      refine ⟨M*(2^n : ℕ)*C σ,mul_nonneg (mul_nonneg hM0 (Nat.cast_nonneg _)) (hC σ),?_⟩
      intro ε _ Q hQ
      apply (averagedSparseChain_bound Γ hΓ Q hK hn hR y₀ μ v hs hinj ψ M hM0 hM).trans
      calc
        _ ≤ M*(2^n : ℕ)*(C σ*ε) := mul_le_mul_of_nonneg_left (hQ σ)
          (mul_nonneg hM0 (Nat.cast_nonneg _))
        _ = _ := by ring
    · refine ⟨0,le_rfl,?_⟩
      intro ε _ Q _
      rw [wedge_eq_zero_of_not_injective _ hinj,map_zero,map_zero,norm_zero,zero_mul]
  | zero =>
    refine ⟨0,le_rfl,?_⟩
    intro ε _ Q _
    simp only [map_zero,norm_zero,zero_mul,le_refl]
  | add a b _ _ ha hb =>
    obtain ⟨A,hA,hA'⟩ := ha
    obtain ⟨B,hB,hB'⟩ := hb
    refine ⟨A+B,add_nonneg hA hB,?_⟩
    intro ε hε Q hQ
    rw [map_add,map_add,add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hA' ε hε Q hQ) (hB' ε hε Q hQ))
  | smul r a _ ha =>
    obtain ⟨A,hA,hA'⟩ := ha
    refine ⟨‖r‖*A,mul_nonneg (norm_nonneg _) hA,?_⟩
    intro ε hε Q hQ
    rw [map_smul,map_smul,norm_smul,mul_assoc]
    exact mul_le_mul_of_nonneg_left (hA' ε hε Q hQ) (norm_nonneg _)

include hK hn hR y₀ in
lemma vanishing_of_zero_strata_tf_oai
    (hInv : (augmentedComplex K).IsInvariant (H := H))
    (hμ : ∀h : H,MeasurePreserving (fun x : X=>h • x) μ μ)
    (C : SourceTop K n → ℝ) (hC : ∀σ,0≤C σ)
    (hzero : ∀ε : ℝ,0<ε → ∃Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
      (realizationDistance Γ hΓ K n) R n,
      ∀σ : SourceTop K n,(∫x,(Measure.count ((Q.pair 0).P.val x∩
        convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))).toReal ∂μ)≤C σ*ε)
    (ψ : Degree Y (n+1) →ₗ[ℂ] ℂ)
    (hψ : ∀(h : H) c,ψ (relabel (n+1) (fun y=>h • y) c)=ψ c)
    (hψd : ∀c,ψ (d (n+1) c)=0)
    (c : (augmentedComplex K).chains (n+1))
    (hc : (⟨d n c,(augmentedComplex K).d_mem n c.property⟩ :
      (augmentedComplex K).chains n)∈(augmentedComplex K).relations hInv n) : ψ c=0 := by
  obtain ⟨B,hB,hbound⟩ := exists_chain_bound (H := H) Γ hΓ hK hn hR y₀ μ C hC ψ c c.property
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  by_contra hh
  have hp : 0<‖ψ c‖ := lt_of_not_ge hh
  let ε := ‖ψ c‖/(2*(B+1))
  have hε : 0<ε := div_pos hp (by positivity)
  obtain ⟨Q,hQ⟩ := hzero ε hε
  have hb := hbound ε hε Q hQ
  rw [averagedSparseChain_comparison Γ hΓ Q hK hn hR y₀ μ hInv hμ n ψ hψ hψd c hc] at hb
  have he : ε*(2*(B+1))=‖ψ c‖ := div_mul_cancel₀ _ (by positivity)
  nlinarith

end BassTrace.Sparse

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.BassTrace.Sparse.vanishing_of_zero_strata_tf_oai.{u_1, u_2, u_3} := @OAI.BassTrace.Sparse.vanishing_of_zero_strata_tf_oai.{u_1, u_2, u_3}
