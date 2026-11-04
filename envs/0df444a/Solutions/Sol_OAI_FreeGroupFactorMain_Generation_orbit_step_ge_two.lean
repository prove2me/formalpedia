-- Prove2me | solution 1 for OAI.FreeGroupFactorMain.Generation.orbit_step_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T03:31:40.540703+00:00
-- url     : https://prove2.me/submissions/5377bd37-a0d6-4185-9a64-befbee8e5cc0

import Mathlib
import Definitions.Def_FreeGroupFactorProof18
import Theorems.Thm_OAI_FreeGroupFactorMain_haar_centered_laurent
import Theorems.Thm_OAI_FreeGroupFactorMain_one_step_from_laurent
import Theorems.Thm_OAI_FreeGroupFactorMain_one_step

set_option linter.all false

section
namespace OAI

noncomputable section

universe uG uH

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

open scoped ENNReal

theorem canonicalTrace_eq_inner {G : Type uG} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) :
    canonicalTrace T = inner ℂ (lp.single 2 (1 : G) (1 : ℂ))
      ((T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))) := by
  classical
  simp only [canonicalTrace, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
  apply congrArg (fun v : GroupHilbert G => ((T : GroupOperator G) v) 1)
  ext b
  simp [lp.single_apply, Pi.single_apply]

theorem canonicalTrace_star_mul {G : Type uG} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) :
    canonicalTrace (star T * T) =
      (‖(T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))‖ ^ 2 : ℂ) := by
  rw [canonicalTrace_eq_inner]
  change inner ℂ (lp.single 2 (1 : G) (1 : ℂ))
    (star (T : GroupOperator G) ((T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ)))) = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq_to_K _

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

namespace FreeGroupFactorMain

noncomputable section

universe uG uH

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

open scoped ComplexConjugate

theorem deltaOne_eq {G : Type uG} [Group G] [DecidableEq G] :
    (deltaOne : GroupHilbert G) = lp.single 2 1 1 := by
  ext x
  simp [deltaOne, lp.single_apply, Pi.single_apply]

open scoped ComplexConjugate ENNReal

open scoped ComplexConjugate

end

end FreeGroupFactorMain

end OAI
end

section
namespace OAI

namespace FreeGroupFactorMain

noncomputable section

universe uA uB uG uH uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

theorem freeCocycle_mul {ι : Type uι} (h : ι → Coeff (FreeGroup ι)) (g b : FreeGroup ι) :
    freeCocycle h (g * b) = freeCocycle h g + coefficientShift g (freeCocycle h b) := by
  unfold freeCocycle
  rw [map_mul]
  rw [SemidirectProduct.mul_left, cocycleGraph_right]
  rfl

theorem freeCocycle_inv {ι : Type uι} (h : ι → Coeff (FreeGroup ι)) (g : FreeGroup ι) :
    freeCocycle h g⁻¹ = -coefficientShift g⁻¹ (freeCocycle h g) := by
  have he := freeCocycle_mul h g⁻¹ g
  simp only [inv_mul_cancel, freeCocycle_one] at he
  exact eq_neg_of_add_eq_zero_left he.symm

namespace UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

end UnitaryEvaluation

section
open UnitaryEvaluation

variable {A : Type uA} {B : Type uB} [CStarAlgebra A] [CStarAlgebra B]

end
section

variable {A : Type uA} [CStarAlgebra A]

end

namespace UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι} [Fintype ι] [DecidableEq ι]

end UnitaryEvaluation

section
open UnitaryEvaluation

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end

theorem twoNorm_le_norm {G : Type uG} [Group G] (T : groupVonNeumann G) :
    twoNorm T ≤ ‖T‖ := by
  calc
    _ ≤ ‖(T : GroupOperator G)‖ * ‖(deltaOne : GroupHilbert G)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = _ := by simp [deltaOne, lp.norm_single]

theorem twoNorm_sq {G : Type uG} [Group G] (T : groupVonNeumann G) :
    (twoNorm T : ℂ)^2 = canonicalTrace (star T*T) := by
  classical
  rw [canonicalTrace_star_mul, ← deltaOne_eq]
  rfl

theorem twoNorm_iso {G : Type uG} {H : Type uH} [Group G] [Group H]
    (Φ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann H)
    (hΦ : ∀ T, canonicalTrace (Φ T) = canonicalTrace T) (T : groupVonNeumann G) :
    twoNorm (Φ T) = twoNorm T := by
  have hs : Φ (star T) = star (Φ T) := Φ.map_star' T
  have hm : Φ (star T * T) = Φ (star T) * Φ T := Φ.map_mul' (star T) T
  have hsq : (twoNorm (Φ T) : ℂ)^2 = (twoNorm T : ℂ)^2 := by
    rw [twoNorm_sq, twoNorm_sq, ← hs, ← hm, hΦ]
  have hr := congrArg Complex.re hsq
  norm_cast at hr
  nlinarith [norm_nonneg (groupL2 (Φ T)), norm_nonneg (groupL2 T)]

end

end FreeGroupFactorMain

end OAI
end

section
namespace OAI

noncomputable section

universe uE uG uI uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

def coefficientSqNorm {G : Type uG} (h : G →₀ ℝ) : ℝ := h.sum (fun _ r => r ^ 2)

@[simp] theorem coefficientSqNorm_zero {G : Type uG} : coefficientSqNorm (0 : G →₀ ℝ) = 0 := by
  simp [coefficientSqNorm]

@[simp] theorem coefficientSqNorm_single {G : Type uG} (g : G) (c : ℝ) :
    coefficientSqNorm (Finsupp.single g c) = c ^ 2 := by
  simp [coefficientSqNorm]

@[simp] theorem coefficientSqNorm_smul {G : Type uG} (c : ℝ) (h : G →₀ ℝ) :
    coefficientSqNorm (c • h) = c ^ 2 * coefficientSqNorm h := by
  classical
  rw [coefficientSqNorm, Finsupp.sum_of_support_subset _ Finsupp.support_smul
    (fun (_ : G) (r : ℝ) => r ^ 2) (by simp)]
  simp [Finsupp.smul_apply, mul_pow, coefficientSqNorm, Finsupp.sum, Finset.mul_sum]

theorem coefficientSqNorm_sum_le {I : Type uI} {G : Type uG} (s : Finset I) (f : I → G →₀ ℝ) :
    coefficientSqNorm (∑ i ∈ s, f i) ≤ (s.card : ℝ) * ∑ i ∈ s, coefficientSqNorm (f i) := by
  classical
  let t := s.biUnion (fun i => (f i).support)
  have hsupp (i : I) (hi : i ∈ s) : (f i).support ⊆ t :=
    Finset.subset_biUnion_of_mem (fun i => (f i).support) hi
  have hsum : (∑ i ∈ s, f i).support ⊆ t := by
    intro g hg
    obtain ⟨i, hi, hgi⟩ := Finsupp.mem_support_finsetSum g hg
    exact hsupp i hi hgi
  rw [coefficientSqNorm, Finsupp.sum_of_support_subset _ hsum _ (by simp)]
  have hq (g : G) : ((∑ i ∈ s, f i) g) ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, (f i g) ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => f i g)
  calc
    _ ≤ ∑ g ∈ t, (s.card : ℝ) * ∑ i ∈ s, (f i g) ^ 2 := Finset.sum_le_sum (fun g _ => hq g)
    _ = (s.card : ℝ) * ∑ i ∈ s, ∑ g ∈ t, (f i g) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact (Finsupp.sum_of_support_subset (f i) (hsupp i hi)
        (fun (_ : G) (r : ℝ) => r ^ 2) (by simp)).symm

theorem coefficientSqNorm_add_le {G : Type uG} (f g : G →₀ ℝ) :
    coefficientSqNorm (f + g) ≤ 2 * (coefficientSqNorm f + coefficientSqNorm g) := by
  simpa using coefficientSqNorm_sum_le (Finset.univ : Finset Bool) (fun b => if b then f else g)

namespace Radial

section
variable {ι : Type uι} [DecidableEq ι] [Fintype ι]

def paths (i : ι) : ℕ → Finset (List ι)
  | 0 => {[]}
  | k + 1 => (Finset.univ.erase i).biUnion (fun j => (paths j k).image (List.cons j))

def sphere : ℕ → Finset (List ι)
  | 0 => {[]}
  | k + 1 => Finset.univ.biUnion (fun j : ι => (paths j k).image (List.cons j))

theorem paths_mem_length (i : ι) (k : ℕ) {w : List ι} (hw : w ∈ paths i k) :
    w.length = k := by
  induction k generalizing i w with
  | zero => simpa [paths] using hw
  | succ k ih =>
    simp only [paths, Finset.mem_biUnion, Finset.mem_image] at hw
    obtain ⟨j, _, v, hv, rfl⟩ := hw
    simp [ih j hv]

theorem sphere_mem_length (k : ℕ) {w : List ι} (hw : w ∈ sphere (ι := ι) k) :
    w.length = k := by
  cases k with
  | zero => simpa [sphere] using hw
  | succ k =>
    simp only [sphere, Finset.mem_biUnion, Finset.mem_image] at hw
    obtain ⟨j, _, v, hv, rfl⟩ := hw
    simp [paths_mem_length j k hv]

omit [Fintype ι] in
theorem cons_images_disjoint {i j : ι} (hij : i ≠ j) (s t : Finset (List ι)) :
    Disjoint (s.image (List.cons i)) (t.image (List.cons j)) := by
  apply Finset.disjoint_left.mpr
  intro w hw ht
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨u, _, hu⟩ := Finset.mem_image.mp ht
  exact hij (List.cons.inj hu).1.symm

theorem card_paths (i : ι) (k : ℕ) :
    (paths i k).card = (Fintype.card ι - 1) ^ k := by
  induction k generalizing i with
  | zero => simp [paths]
  | succ k ih =>
    rw [paths, Finset.card_biUnion]
    · simp only [Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2), ih]
      simp [pow_succ, Nat.mul_comm]
    · intro a _ b _ hab
      exact cons_images_disjoint hab _ _

theorem card_sphere_succ (k : ℕ) :
    (sphere (ι := ι) (k + 1)).card = Fintype.card ι * (Fintype.card ι - 1) ^ k := by
  rw [sphere, Finset.card_biUnion]
  · simp only [Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2), card_paths]
    simp
  · intro a _ b _ hab
    exact cons_images_disjoint hab _ _

def signed (b : Bool) : List ι → List (ι × Bool)
  | [] => []
  | i :: w => (i, b) :: signed (!b) w

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem signed_length (b : Bool) (w : List ι) : (signed b w).length = w.length := by
  induction w generalizing b with
  | nil => rfl
  | cons i w ih => simp [signed, ih]

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem signed_map_fst (b : Bool) (w : List ι) :
    (signed b w).map Prod.fst = w := by
  induction w generalizing b with
  | nil => rfl
  | cons i w ih => simp [signed, ih]

omit [DecidableEq ι] [Fintype ι] in
theorem signed_injective (b : Bool) : Function.Injective (signed (ι := ι) b) := by
  intro u v huv
  simpa using congrArg (List.map Prod.fst) huv

theorem signed_reduced_paths (b : Bool) (i : ι) (k : ℕ) {w : List ι}
    (hw : w ∈ paths i k) : FreeGroup.IsReduced ((i, b) :: signed (!b) w) := by
  induction k generalizing b i w with
  | zero =>
    have : w = [] := by simpa [paths] using hw
    subst w
    exact FreeGroup.IsReduced.singleton
  | succ k ih =>
    simp only [paths, Finset.mem_biUnion, Finset.mem_image, Finset.mem_erase,
      Finset.mem_univ, and_true] at hw
    obtain ⟨j, hji, v, hv, rfl⟩ := hw
    rw [signed, FreeGroup.isReduced_cons_cons]
    exact ⟨fun hij => False.elim (hji hij.symm), ih (!b) j hv⟩

theorem signed_reduced_sphere (b : Bool) (k : ℕ) {w : List ι}
    (hw : w ∈ sphere (ι := ι) k) : FreeGroup.IsReduced (signed b w) := by
  cases k with
  | zero =>
    have : w = [] := by simpa [sphere] using hw
    subst w
    exact FreeGroup.IsReduced.nil
  | succ k =>
    simp only [sphere, Finset.mem_biUnion, Finset.mem_image] at hw
    obtain ⟨j, _, v, hv, rfl⟩ := hw
    exact signed_reduced_paths b j k hv

def vertex (b : Bool) (w : List ι) : FreeGroup ι := FreeGroup.mk (signed b w)

theorem toWord_vertex (b : Bool) (k : ℕ) {w : List ι}
    (hw : w ∈ sphere (ι := ι) k) : (vertex b w).toWord = signed b w := by
  rw [vertex, FreeGroup.toWord_mk, (signed_reduced_sphere b k hw).reduce_eq]

theorem vertex_injOn (b : Bool) (k : ℕ) :
    Set.InjOn (vertex (ι := ι) b) (↑(sphere (ι := ι) k) : Set (List ι)) := by
  intro u hu v hv huv
  have hh := congrArg FreeGroup.toWord huv
  rw [toWord_vertex b k hu, toWord_vertex b k hv] at hh
  exact signed_injective b hh

theorem sum_sphere_succ {E : Type uE} [AddCommMonoid E] (f : List ι → E) (k : ℕ) :
    ∑ w ∈ sphere (ι := ι) (k + 1), f w =
      ∑ j : ι, ∑ w ∈ paths j k, f (j :: w) := by
  rw [sphere, Finset.sum_biUnion (fun i _ j _ hij => cons_images_disjoint hij _ _)]
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_image (fun _ _ _ _ h => (List.cons.inj h).2)

theorem sum_paths_succ {E : Type uE} [AddCommMonoid E] (f : List ι → E) (i : ι) (k : ℕ) :
    ∑ w ∈ paths i (k + 1), f w =
      ∑ j ∈ Finset.univ.erase i, ∑ w ∈ paths j k, f (j :: w) := by
  rw [paths, Finset.sum_biUnion (fun a _ b _ hab => cons_images_disjoint hab _ _)]
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_image (fun _ _ _ _ h => (List.cons.inj h).2)

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem vertex_nil (b : Bool) : vertex (ι := ι) b [] = 1 := rfl

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem vertex_cons_true (i : ι) (w : List ι) :
    vertex true (i :: w) = FreeGroup.of i * vertex false w := by
  rfl

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem vertex_cons_false (i : ι) (w : List ι) :
    vertex false (i :: w) = (FreeGroup.of i)⁻¹ * vertex true w := by
  rfl

def shell (b : Bool) (k : ℕ) : FreeGroup ι →₀ ℝ :=
  ∑ w ∈ sphere k, Finsupp.single (vertex b w) 1

def shift (g : FreeGroup ι) : (FreeGroup ι →₀ ℝ) →ₗ[ℝ] (FreeGroup ι →₀ ℝ) :=
  (Finsupp.domLCongr (Equiv.mulLeft g)).toLinearMap

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem shift_single (g a : FreeGroup ι) (r : ℝ) :
    shift g (Finsupp.single a r) = Finsupp.single (g * a) r := by
  exact Finsupp.equivMapDomain_single (Equiv.mulLeft g) a r

def sumShift : (FreeGroup ι →₀ ℝ) →ₗ[ℝ] (FreeGroup ι →₀ ℝ) :=
  ∑ i : ι, shift (FreeGroup.of i)

omit [DecidableEq ι] in
@[simp] theorem sumShift_apply (h : FreeGroup ι →₀ ℝ) :
    sumShift h = ∑ i : ι, shift (FreeGroup.of i) h := by
  simp [sumShift]

@[simp] theorem shell_zero (b : Bool) : shell (ι := ι) b 0 = Finsupp.single 1 1 := by
  simp [shell, sphere]

theorem shell_succ (b : Bool) (k : ℕ) :
    shell (ι := ι) b (k + 1) =
      ∑ j : ι, ∑ w ∈ paths j k, Finsupp.single (vertex b (j :: w)) 1 := by
  exact sum_sphere_succ _ _

theorem outward_shell (k : ℕ) :
    (∑ j : ι, ∑ w ∈ paths j k, ∑ i ∈ Finset.univ.erase j,
      Finsupp.single (FreeGroup.of i * vertex false (j :: w)) (1 : ℝ)) =
        shell (ι := ι) true (k + 2) := by
  rw [shell_succ]
  simp only [sum_paths_succ]
  simp_rw [vertex_cons_true]
  simp_rw [Finset.sum_comm (s := paths _ _) (t := Finset.univ.erase _)]
  apply Finset.sum_comm'
  intro x y
  simp [ne_comm, and_comm]

theorem sumShift_shell (k : ℕ) :
    sumShift (shell (ι := ι) false (k + 1)) =
      (∑ j : ι, ∑ w ∈ paths j k, Finsupp.single (vertex true w) (1 : ℝ)) +
        shell (ι := ι) true (k + 2) := by
  rw [shell_succ, map_sum]
  simp only [map_sum, sumShift_apply, shift_single]
  have hs (j : ι) (w : List ι) :
      (∑ i : ι, Finsupp.single (FreeGroup.of i * vertex false (j :: w)) (1 : ℝ)) =
        Finsupp.single (vertex true w) 1 +
          ∑ i ∈ Finset.univ.erase j,
            Finsupp.single (FreeGroup.of i * vertex false (j :: w)) 1 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    simp [add_comm, vertex_cons_false]
  simp_rw [hs, Finset.sum_add_distrib]
  rw [outward_shell]

theorem sumShift_shell_one :
    sumShift (shell (ι := ι) false 1) =
      (Fintype.card ι : ℝ) • Finsupp.single 1 1 + shell (ι := ι) true 2 := by
  rw [show 1 = 0 + 1 from rfl, sumShift_shell]
  simp [paths, Nat.cast_smul_eq_nsmul]

theorem inward_shell [Nonempty ι] (k : ℕ) :
    (∑ j : ι, ∑ w ∈ paths j (k + 1), Finsupp.single (vertex true w) (1 : ℝ)) =
      ((Fintype.card ι - 1 : ℕ) : ℝ) • shell (ι := ι) true (k + 1) := by
  simp_rw [sum_paths_succ, Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ]
  rw [← shell_succ, ← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_sub Fintype.card_pos,
      Nat.cast_one, sub_smul, one_smul]

theorem sumShift_shell_succ [Nonempty ι] (k : ℕ) :
    sumShift (shell (ι := ι) false (k + 2)) =
      ((Fintype.card ι - 1 : ℕ) : ℝ) • shell (ι := ι) true (k + 1) +
        shell (ι := ι) true (k + 3) := by
  rw [show k + 2 = (k + 1) + 1 from rfl, sumShift_shell, inward_shell]

def vertices (b : Bool) (k : ℕ) : Finset (FreeGroup ι) :=
  (sphere k).image (vertex b)

theorem shell_eq_sum_vertices (b : Bool) (k : ℕ) :
    shell (ι := ι) b k = ∑ g ∈ vertices b k, Finsupp.single g 1 := by
  rw [vertices, Finset.sum_image (vertex_injOn b k)]
  rfl

@[simp] theorem shell_apply (b : Bool) (k : ℕ) (g : FreeGroup ι) :
    shell (ι := ι) b k g = if g ∈ vertices b k then 1 else 0 := by
  rw [shell_eq_sum_vertices]
  simp [Finsupp.single_apply]

@[simp] theorem shell_support (b : Bool) (k : ℕ) :
    (shell (ι := ι) b k).support = vertices b k := by
  ext g
  simp only [Finsupp.mem_support_iff, shell_apply]
  split_ifs <;> simp_all

theorem card_vertices (b : Bool) (k : ℕ) :
    (vertices (ι := ι) b k).card = (sphere (ι := ι) k).card :=
  Finset.card_image_iff.mpr (vertex_injOn b k)

theorem vertices_disjoint (b c : Bool) {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (vertices (ι := ι) b k) (vertices (ι := ι) c l) := by
  apply Finset.disjoint_left.mpr
  intro g hg hk
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hg
  obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp hk
  have heq := congrArg (fun x : FreeGroup ι => x.toWord.length) hveq
  rw [toWord_vertex c l hv, toWord_vertex b k hu, signed_length,
    signed_length, sphere_mem_length l hv, sphere_mem_length k hu] at heq
  exact hkl heq.symm

end

def rightShell (m k : ℕ) : FreeGroup (Fin m) →₀ ℝ :=
  (1 / ((m : ℝ) * ((m : ℝ) - 1) ^ k)) • shell false (2 * k + 1)

def leftShell (m k : ℕ) : FreeGroup (Fin m) →₀ ℝ :=
  (1 / ((m : ℝ) * ((m : ℝ) - 1) ^ k)) • shell true (2 * k + 2)

theorem sqNorm_shell_succ (m k : ℕ) (hm : 1 ≤ m) (b : Bool) :
    coefficientSqNorm (shell (ι := Fin m) b (k + 1)) =
      (m : ℝ) * ((m : ℝ) - 1) ^ k := by
  classical
  rw [coefficientSqNorm, Finsupp.sum, shell_support]
  have hs : (∑ g ∈ vertices (ι := Fin m) b (k + 1), (shell b (k + 1) g) ^ 2) =
      ((vertices (ι := Fin m) b (k + 1)).card : ℝ) := by
    simp only [shell_apply]
    simp
  rw [hs, card_vertices, card_sphere_succ]
  simp [Nat.cast_sub hm]

theorem sumShift_rightShell_zero (m : ℕ) (hm : 2 ≤ m) :
    sumShift (rightShell m 0) = Finsupp.single 1 1 + leftShell m 0 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  rw [rightShell, map_smul]
  simp only [mul_zero, zero_add]
  rw [sumShift_shell_one, smul_add, smul_smul]
  simp [leftShell, hm0]

theorem sumShift_rightShell_succ (m k : ℕ) (hm : 2 ≤ m) :
    sumShift (rightShell m (k + 1)) = leftShell m k + leftShell m (k + 1) := by
  let : NeZero m := ⟨by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hq0 : (m : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  rw [rightShell, map_smul, show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
    sumShift_shell_succ, smul_add, smul_smul]
  simp only [Fintype.card_fin, Nat.cast_sub hm1, Nat.cast_one, leftShell]
  have heq : 1 / ((m : ℝ) * ((m : ℝ) - 1) ^ (k + 1)) * ((m : ℝ) - 1) =
      1 / ((m : ℝ) * ((m : ℝ) - 1) ^ k) := by
    rw [pow_succ]
    field_simp
  rw [heq]
  congr 2

theorem sqNorm_leftShell (m k : ℕ) (hm : 2 ≤ m) :
    coefficientSqNorm (leftShell m k) = ((m : ℝ) - 1) / (m : ℝ) := by
  have hm1 : 1 ≤ m := by omega
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hq0 : (m : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  rw [leftShell, coefficientSqNorm_smul,
    show 2 * k + 2 = (2 * k + 1) + 1 by omega, sqNorm_shell_succ m (2 * k + 1) hm1,
    pow_succ ((m : ℝ) - 1) (2 * k), show 2 * k = k * 2 by omega, pow_mul]
  field_simp

def partialInverse (m N : ℕ) : FreeGroup (Fin m) →₀ ℝ :=
  ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k • rightShell m k

@[simp] theorem partialInverse_zero (m : ℕ) : partialInverse m 0 = 0 := by
  simp [partialInverse]

theorem partialInverse_succ (m N : ℕ) :
    partialInverse m (N + 1) = partialInverse m N + (-1 : ℝ) ^ N • rightShell m N := by
  exact Finset.sum_range_succ _ _

theorem sumShift_partialInverse (m N : ℕ) (hm : 2 ≤ m) :
    sumShift (partialInverse m (N + 1)) =
      Finsupp.single 1 1 + (-1 : ℝ) ^ N • leftShell m N := by
  induction N with
  | zero => simp only [partialInverse_succ, partialInverse_zero, pow_zero, one_smul,
      zero_add, sumShift_rightShell_zero m hm]
  | succ N ih =>
    rw [partialInverse_succ, map_add, ih, map_smul, sumShift_rightShell_succ m N hm]
    simp only [pow_succ, mul_neg_one, neg_smul, smul_add]
    abel

theorem leftShell_disjoint (m : ℕ) {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (leftShell m j).support (leftShell m k).support := by
  exact Finset.disjoint_of_subset_left Finsupp.support_smul
    (Finset.disjoint_of_subset_right Finsupp.support_smul
      (by rw [shell_support, shell_support]; exact vertices_disjoint _ _ (by omega)))

def averagedInverse (m N : ℕ) : FreeGroup (Fin m) →₀ ℝ :=
  (1 / (N + 1 : ℝ)) • ∑ k ∈ Finset.range (N + 1), partialInverse m (k + 1)

theorem sumShift_averagedInverse (m N : ℕ) (hm : 2 ≤ m) :
    sumShift (averagedInverse m N) - Finsupp.single 1 1 =
      (1 / (N + 1 : ℝ)) •
        ∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k • leftShell m k := by
  rw [averagedInverse, map_smul, map_sum]
  simp_rw [sumShift_partialInverse m _ hm]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_add, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have hN : (N + 1 : ℝ) ≠ 0 := by positivity
  simp [hN]

end Radial
end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uG uH uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

theorem freeCocycle_pow_of_zero {ι : Type uι} (h : ι → Coeff (FreeGroup ι))
    (g : FreeGroup ι) (hg : freeCocycle h g = 0) (k : ℕ) :
    freeCocycle h (g ^ k) = 0 := by
  induction k with
  | zero => simp
  | succ k ih => simp [pow_succ, freeCocycle_mul, ih, hg]

namespace PrefixSeparation

end PrefixSeparation

def pushCoefficients {G : Type uG} {H : Type uH} [Group G] [Group H] (f : G →* H) :
    (G →₀ ℝ) →ₗ[ℝ] (H →₀ ℝ) := Finsupp.lmapDomain ℝ ℝ f

@[simp] theorem pushCoefficients_single {G : Type uG} {H : Type uH} [Group G] [Group H]
    (f : G →* H) (g : G) (c : ℝ) :
    pushCoefficients f (Finsupp.single g c) = Finsupp.single (f g) c := by
  exact Finsupp.mapDomain_single

theorem pushCoefficients_shift {ι : Type uι} {H : Type uH} [Group H]
    (f : FreeGroup ι →* H) (g : FreeGroup ι) (h : FreeGroup ι →₀ ℝ) :
    pushCoefficients f (Radial.shift g h) = coefficientShift (f g) (pushCoefficients f h) := by
  induction h using Finsupp.induction_linear with
  | zero => simp
  | add h k ih ik => simp only [map_add, ih, ik]
  | single b c => simp [Radial.shift_single]

theorem sqNorm_pushCoefficients {G : Type uG} {H : Type uH} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (h : G →₀ ℝ) :
    coefficientSqNorm (pushCoefficients f h) = coefficientSqNorm h := by
  exact Finsupp.sum_mapDomain_index_inj hf

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uG uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain.Generation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

variable {G : Type uG} [Group G]

end FreeGroupFactorMain.Generation

namespace FreeGroupFactorMain
open UnitaryEvaluation

theorem laurentValue_eq_value {A : Type uA} [CStarAlgebra A] (C : unitary A) (l : ℤ →₀ ℂ) :
    laurentValue C l = LaurentApprox.value C l := rfl

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uB uC uG uH uI uK uP uX uY uι uκ

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain.Generation

section
variable {A : Type uA} {B : Type uB} [CStarAlgebra A] [CStarAlgebra B] {ι : Type uι} {κ : Type uκ}

end

theorem word_initial (n : ℕ) (g : FreeGroup (Fin n)) :
    word (initial n) g = groupUnitary (FreeGroup.map Option.some g) := by
  have he : word (initial n) =
      (unitary (Ambient n)).subtype.comp
        ((groupUnitaryUHom (FreeGroup (Option (Fin n)))).comp (FreeGroup.map Option.some)) := by
    apply FreeGroup.ext_hom
    intro j
    simp only [word_of,MonoidHom.comp_apply,FreeGroup.map.of]
    rfl
  exact DFunLike.congr_fun he g

end FreeGroupFactorMain.Generation

namespace FreeGroupFactorMain

open Generation

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

namespace FreeGroupFactorMain

noncomputable section

universe uG uH uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

attribute [local instance] Classical.propDecidable

namespace RankTwo

section
open Monoid.CoprodI

abbrev SyllableGroup := Monoid.CoprodI SyllableGroups

def syllable (i : Bool) (z : ℤ) : SyllableGroup :=
  Monoid.CoprodI.of (i := i) (Multiplicative.ofAdd z)

def singleWord (i : Bool) (z : ℤ) (hz : z ≠ 0) : NW i i :=
  NeWord.singleton (Multiplicative.ofAdd z) hz

@[simp] theorem singleWord_prod (i : Bool) (z : ℤ) (hz : z ≠ 0) :
    (singleWord i z hz).prod = syllable i z := by
  exact NeWord.prod_singleton _ _

@[simp] theorem syllable_add (i : Bool) (z w : ℤ) :
    syllable i (z+w) = syllable i z * syllable i w := by
  exact map_mul (Monoid.CoprodI.of (i := i)) (Multiplicative.ofAdd z) (Multiplicative.ofAdd w)

@[simp] theorem syllable_neg (i : Bool) (z : ℤ) :
    syllable i (-z) = (syllable i z)⁻¹ := by
  exact map_inv _ _

@[simp] theorem syllable_zero (i : Bool) : syllable i 0 = 1 := map_one _

theorem neWord_prod_ne_one {i j : Bool} (w : NW i j) : w.prod ≠ 1 := by
  classical
  intro h
  have hinj : Function.Injective (Word.prod : Word SyllableGroups → SyllableGroup) :=
    (Word.equiv (M := SyllableGroups)).symm.injective
  have heq : w.toWord = Word.empty := hinj (by simpa [NeWord.prod] using h)
  exact w.toList_ne_nil (congrArg Word.toList heq)

variable {ι : Type uι}

def longBlock (start finish : ι → ℤ) (core : ι → NW true true) (i : ι) : SyllableGroup :=
  syllable true 1 * syllable false (start i) * (core i).prod * syllable false (finish i)

def PositiveHead (start : ι → ℤ) (i : ι) (g : SyllableGroup) : Prop :=
  ∃ j, ∃ W : NW false j, W.head = Multiplicative.ofAdd (start i) ∧
    g = syllable true 1 * W.prod

def NegativeHead (finish : ι → ℤ) (i : ι) (g : SyllableGroup) : Prop :=
  ∃ j, ∃ W : NW true j, g = syllable false (-(finish i)) * W.prod

theorem positiveHead_ne_one {start : ι → ℤ} {i : ι} {g : SyllableGroup}
    (h : PositiveHead start i g) : g ≠ 1 := by
  obtain ⟨j,W,_hW,rfl⟩ := h
  exact neWord_prod_ne_one ((singleWord true 1 (by norm_num)).append (by decide) W)

theorem negativeHead_ne_one {finish : ι → ℤ} {i : ι} (hi : finish i ≠ 0)
    {g : SyllableGroup} (h : NegativeHead finish i g) : g ≠ 1 := by
  obtain ⟨j,W,rfl⟩ := h
  exact neWord_prod_ne_one ((singleWord false (-finish i) (neg_ne_zero.mpr hi)).append (by decide) W)

variable (start finish : ι → ℤ) (core : ι → NW true true)
variable (hs : ∀ i, start i ≠ 0) (ht : ∀ i, finish i ≠ 0)
include hs ht

theorem longBlock_positive (i : ι) :
    PositiveHead start i (longBlock start finish core i) := by
  let W := ((singleWord false (start i) (hs i)).append (by decide) (core i)).append
    (by decide) (singleWord false (finish i) (ht i))
  refine ⟨false,W,?_,?_⟩
  · rfl
  · simp [W,longBlock,mul_assoc]

omit ht in
theorem longBlock_negative (i : ι) :
    NegativeHead finish i (longBlock start finish core i)⁻¹ := by
  let W := ((core i).inv.append (by decide) (singleWord false (-start i) (neg_ne_zero.mpr (hs i)))).append
    (by decide) (singleWord true (-1) (by norm_num))
  refine ⟨true,W,?_⟩
  simp [W,longBlock,mul_inv_rev,mul_assoc]

theorem positive_mul_positive (i j : ι) {g : SyllableGroup}
    (h : PositiveHead start j g) :
    PositiveHead start i (longBlock start finish core i * g) := by
  obtain ⟨k,V,_hV,rfl⟩ := h
  let W := ((((singleWord false (start i) (hs i)).append (by decide) (core i)).append
    (by decide) (singleWord false (finish i) (ht i))).append (by decide)
    (singleWord true 1 (by norm_num))).append (by decide) V
  refine ⟨k,W,rfl,?_⟩
  simp [W,longBlock,mul_assoc]

theorem negative_mul_negative (i j : ι) {g : SyllableGroup}
    (h : NegativeHead finish j g) :
    NegativeHead finish i ((longBlock start finish core i)⁻¹ * g) := by
  obtain ⟨k,V,rfl⟩ := h
  let W := ((((core i).inv.append (by decide) (singleWord false (-start i) (neg_ne_zero.mpr (hs i)))).append
    (by decide) (singleWord true (-1) (by norm_num))).append (by decide)
    (singleWord false (-finish j) (neg_ne_zero.mpr (ht j)))).append (by decide) V
  refine ⟨k,W,?_⟩
  simp [W,longBlock,mul_inv_rev,mul_assoc]

omit ht in
theorem positive_mul_negative (i j : ι) (hij : finish i ≠ finish j) {g : SyllableGroup}
    (h : NegativeHead finish j g) :
    PositiveHead start i (longBlock start finish core i * g) := by
  obtain ⟨k,V,rfl⟩ := h
  let W := (((singleWord false (start i) (hs i)).append (by decide) (core i)).append
    (by decide) (singleWord false (finish i-finish j) (sub_ne_zero.mpr hij))).append (by decide) V
  refine ⟨k,W,rfl,?_⟩
  simp [W,longBlock,sub_eq_add_neg,mul_assoc]

omit hs ht in
theorem negative_mul_positive (i j : ι) (hij : start i ≠ start j) {g : SyllableGroup}
    (h : PositiveHead start j g) :
    NegativeHead finish i ((longBlock start finish core i)⁻¹ * g) := by
  obtain ⟨k,V,hV,rfl⟩ := h
  have hno : (Multiplicative.ofAdd (-(start i))) * V.head ≠ 1 := by
    rw [hV]
    change -(start i) + start j ≠ 0
    omega
  let W := (core i).inv.append (by decide) (V.mulHead (Multiplicative.ofAdd (-(start i))) hno)
  refine ⟨k,W,?_⟩
  simp [W,longBlock,mul_inv_rev,syllable,mul_assoc]

variable (hinjs : Function.Injective start) (hinjt : Function.Injective finish)
include hinjs hinjt

def evalLetters (f : ι → SyllableGroup) (L : List (ι × Bool)) : SyllableGroup :=
  (L.map (fun x => cond x.2 (f x.1) (f x.1)⁻¹)).prod

omit hs ht hinjs hinjt in
@[simp] theorem evalLetters_nil (f : ι → SyllableGroup) : evalLetters f [] = 1 := rfl

omit hs ht hinjs hinjt in
@[simp] theorem evalLetters_cons (f : ι → SyllableGroup) (i : ι) (b : Bool) (L : List (ι × Bool)) :
    evalLetters f ((i,b)::L) = (cond b (f i) (f i)⁻¹) * evalLetters f L := rfl

theorem longBlock_head (L : List (ι × Bool)) (i : ι) (b : Bool)
    (hL : FreeGroup.IsReduced ((i,b)::L)) :
    if b then PositiveHead start i (evalLetters (longBlock start finish core) ((i,b)::L))
    else NegativeHead finish i (evalLetters (longBlock start finish core) ((i,b)::L)) := by
  induction L generalizing i b with
  | nil =>
    cases b
    · simpa using longBlock_negative start finish core hs i
    · simpa using longBlock_positive start finish core hs ht i
  | cons a L ih =>
    obtain ⟨j,c⟩ := a
    obtain ⟨hij,hred⟩ := FreeGroup.isReduced_cons_cons.mp hL
    have hrec := ih j c hred
    cases b <;> cases c
    · simpa using negative_mul_negative start finish core hs ht i j hrec
    · have hne : start i ≠ start j := fun h => by simpa using hij (hinjs h)
      simpa using negative_mul_positive start finish core i j hne hrec
    · have hne : finish i ≠ finish j := fun h => by simpa using hij (hinjt h)
      simpa using positive_mul_negative start finish core hs i j hne hrec
    · simpa using positive_mul_positive start finish core hs ht i j hrec

theorem longBlock_injective :
    Function.Injective (FreeGroup.lift (longBlock start finish core)) := by
  classical
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  have hred := FreeGroup.isReduced_toWord (x := g)
  have he : evalLetters (longBlock start finish core) g.toWord = 1 := by
    unfold evalLetters
    rw [← FreeGroup.lift_mk,FreeGroup.mk_toWord]
    exact hg
  cases hw : g.toWord with
  | nil => exact FreeGroup.toWord_eq_nil_iff.mp hw
  | cons a L =>
    obtain ⟨i,b⟩ := a
    rw [hw] at hred he
    have hh := longBlock_head start finish core hs ht hinjs hinjt L i b hred
    cases b
    · exact False.elim (negativeHead_ne_one (ht i) hh he)
    · exact False.elim (positiveHead_ne_one hh he)

end
open Monoid.CoprodI

def piece (E : ℕ → ℤ) (j : ℕ) : SyllableGroup := syllable true 1 * syllable false (E j)

def segment (E : ℕ → ℤ) (s : ℕ) : ℕ → SyllableGroup
  | 0 => 1
  | k+1 => segment E s k * piece E (s+k)

@[simp] theorem segment_zero (E : ℕ → ℤ) (s : ℕ) : segment E s 0 = 1 := rfl
@[simp] theorem segment_succ (E : ℕ → ℤ) (s k : ℕ) :
    segment E s (k+1) = segment E s k * piece E (s+k) := rfl

@[simp] theorem segment_one (E : ℕ → ℤ) (s : ℕ) : segment E s 1 = piece E s := by simp

theorem segment_append (E : ℕ → ℤ) (s j k : ℕ) :
    segment E s (j+k) = segment E s j * segment E (s+j) k := by
  induction k with
  | zero => simp
  | succ k ih => simp only [Nat.add_succ,segment_succ,ih,Nat.add_assoc,mul_assoc]

theorem segment_cons (E : ℕ → ℤ) (s k : ℕ) :
    segment E s (k+1) = piece E s * segment E (s+1) k := by
  simpa [Nat.add_comm] using segment_append E s 1 k

def coreWord (E : ℕ → ℤ) (hE : ∀ j, E j ≠ 0) (s : ℕ) : ℕ → NW true true
  | 0 => singleWord true 1 (by norm_num)
  | k+1 => ((coreWord E hE s k).append (by decide)
      (singleWord false (E (s+k)) (hE (s+k)))).append (by decide)
      (singleWord true 1 (by norm_num))

theorem segment_core (E : ℕ → ℤ) (hE : ∀ j, E j ≠ 0) (s k : ℕ) :
    segment E s (k+1) = (coreWord E hE s k).prod * syllable false (E (s+k)) := by
  induction k with
  | zero => simp [coreWord,piece]
  | succ k ih =>
    rw [segment_succ,ih]
    simp only [coreWord,NeWord.append_prod,singleWord_prod,piece,mul_assoc]

theorem segment_longBlock (E : ℕ → ℤ) (hE : ∀ j, E j ≠ 0) (s k : ℕ) :
    segment E s (k+2) = syllable true 1 * syllable false (E s) *
      (coreWord E hE (s+1) k).prod * syllable false (E (s+k+1)) := by
  rw [show k+2 = (k+1)+1 by omega,segment_cons,segment_core E hE]
  have he : s+1+k = s+k+1 := by omega
  simp only [piece,mul_assoc,he]

def cumulative {G : Type uG} [Group G] (f : ℕ → G) : ℕ → G
  | 0 => 1
  | k+1 => cumulative f k * f k

@[simp] theorem cumulative_zero {G : Type uG} [Group G] (f : ℕ → G) : cumulative f 0 = 1 := rfl
@[simp] theorem cumulative_succ {G : Type uG} [Group G] (f : ℕ → G) (k : ℕ) :
    cumulative f (k+1) = cumulative f k * f k := rfl

def finGenerator (m j : ℕ) : FreeGroup (Fin m) :=
  if h : j < m then FreeGroup.of ⟨j,h⟩ else 1

def prefixGenerator (m j : ℕ) : FreeGroup (Fin m) :=
  if j = 0 then 1 else finGenerator m (j-1)

@[simp] theorem prefixGenerator_zero (m : ℕ) : prefixGenerator m 0 = 1 := by simp [prefixGenerator]
@[simp] theorem prefixGenerator_succ (m j : ℕ) : prefixGenerator m (j+1) = finGenerator m j := by
  simp [prefixGenerator]

@[simp] theorem finGenerator_fin {m : ℕ} (i : Fin m) : finGenerator m i.val = FreeGroup.of i := by
  simp [finGenerator,i.is_lt]

def triangularHom (m : ℕ) : FreeGroup (Fin m) →* FreeGroup (Fin m) :=
  FreeGroup.lift (fun i => cumulative (finGenerator m) (i.val+1))

def differenceHom (m : ℕ) : FreeGroup (Fin m) →* FreeGroup (Fin m) :=
  FreeGroup.lift (fun i => (prefixGenerator m i.val)⁻¹ * prefixGenerator m (i.val+1))

theorem difference_cumulative (m k : ℕ) (hk : k ≤ m) :
    differenceHom m (cumulative (finGenerator m) k) = prefixGenerator m k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkm : k < m := by omega
    rw [cumulative_succ,map_mul,ih (by omega)]
    simp only [finGenerator,dite_eq_left hkm,differenceHom,FreeGroup.lift_apply_of]
    simp

theorem triangularHom_injective (m : ℕ) : Function.Injective (triangularHom m) := by
  have hcomp : (differenceHom m).comp (triangularHom m) = MonoidHom.id _ := by
    ext i
    simp only [MonoidHom.comp_apply,triangularHom,FreeGroup.lift_apply_of,MonoidHom.id_apply]
    rw [difference_cumulative m (i.val+1) (by omega)]
    simp
  intro x y hxy
  have := congrArg (differenceHom m) hxy
  change ((differenceHom m).comp (triangularHom m)) x =
    ((differenceHom m).comp (triangularHom m)) y at this
  simpa only [hcomp,MonoidHom.id_apply] using this

theorem cumulative_injective {G : Type uG} [Group G] (m : ℕ) (f : ℕ → G)
    (hf : Function.Injective (FreeGroup.lift (fun i : Fin m => f i.val))) :
    Function.Injective (FreeGroup.lift (fun i : Fin m => cumulative f (i.val+1))) := by
  have hc (k : ℕ) (hk : k ≤ m) :
      FreeGroup.lift (fun i : Fin m => f i.val) (cumulative (finGenerator m) k) = cumulative f k := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hkm : k < m := by omega
      rw [cumulative_succ,map_mul,ih (by omega),cumulative_succ]
      simp only [finGenerator,dite_eq_left hkm,FreeGroup.lift_apply_of]
  have he : FreeGroup.lift (fun i : Fin m => cumulative f (i.val+1)) =
      (FreeGroup.lift (fun i : Fin m => f i.val)).comp (triangularHom m) := by
    ext i
    simp only [MonoidHom.comp_apply,triangularHom,FreeGroup.lift_apply_of]
    exact (hc (i.val+1) (by omega)).symm
  rw [he]
  exact hf.comp (triangularHom_injective m)

theorem intervalBlocks_injective (E : ℕ → ℤ) (hE : ∀ j, E j ≠ 0)
    (hiE : Function.Injective E) (k : ℕ) (b : Fin (k+1) → ℕ)
    (hb : ∀ i : Fin k, b i.castSucc + 2 ≤ b i.succ) :
    Function.Injective (FreeGroup.lift (fun i : Fin k =>
      segment E (b i.castSucc) (b i.succ - b i.castSucc))) := by
  have hbm : StrictMono b := Fin.strictMono_iff_lt_succ.mpr (fun i => by have := hb i; omega)
  let start (i : Fin k) : ℤ := E (b i.castSucc)
  let finish (i : Fin k) : ℤ := E (b i.succ-1)
  let core (i : Fin k) : NW true true :=
    coreWord E hE (b i.castSucc+1) (b i.succ-b i.castSucc-2)
  have hstart : Function.Injective start := by
    intro i j hij
    have he := congrArg Fin.val (hbm.injective (hiE hij))
    exact Fin.ext he
  have hfinish : Function.Injective finish := by
    intro i j hij
    have he := hiE hij
    have hi := hb i
    have hj := hb j
    have he' : b i.succ = b j.succ := by omega
    have hev := congrArg Fin.val (hbm.injective he')
    apply Fin.ext
    exact Nat.add_right_cancel hev
  have hh := longBlock_injective start finish core (fun i => hE _) (fun i => hE _) hstart hfinish
  have he (i : Fin k) : segment E (b i.castSucc) (b i.succ-b i.castSucc) =
      longBlock start finish core i := by
    have hbi := hb i
    have hn : b i.succ-b i.castSucc = (b i.succ-b i.castSucc-2)+2 := by omega
    rw [hn,segment_longBlock E hE]
    dsimp only [longBlock,start,finish,core]
    have he' : b i.castSucc+(b i.succ-b i.castSucc-2)+1 = b i.succ-1 := by omega
    rw [he']
  simpa only [he] using hh

theorem boundaryPrefixes_injective (E : ℕ → ℤ) (hE : ∀ j, E j ≠ 0)
    (hiE : Function.Injective E) (k : ℕ) (b : Fin (k+1) → ℕ)
    (hb0 : b 0 = 0) (hb : ∀ i : Fin k, b i.castSucc + 2 ≤ b i.succ) :
    Function.Injective (FreeGroup.lift (fun i : Fin k => segment E 0 (b i.succ))) := by
  let f (j : ℕ) : SyllableGroup := if h : j < k then
      segment E (b (⟨j,h⟩ : Fin k).castSucc) (b (⟨j,h⟩ : Fin k).succ-b (⟨j,h⟩ : Fin k).castSucc)
    else 1
  have hf : Function.Injective (FreeGroup.lift (fun i : Fin k => f i.val)) := by
    simpa only [f,dite_eq_left (Fin.is_lt _)] using intervalBlocks_injective E hE hiE k b hb
  have hc (j : ℕ) (hj : j ≤ k) : cumulative f j = segment E 0 (b ⟨j,by omega⟩) := by
    induction j with
    | zero => simp [hb0]
    | succ j ih =>
      have hjk : j < k := by omega
      have hbj := hb ⟨j,hjk⟩
      change b (⟨j,by omega⟩ : Fin (k+1))+2 ≤ b (⟨j+1,by omega⟩ : Fin (k+1)) at hbj
      rw [cumulative_succ,ih (by omega)]
      simp only [f,dite_eq_left hjk]
      have happ := segment_append E 0 (b (⟨j,by omega⟩ : Fin (k+1)))
        (b (⟨j+1,by omega⟩ : Fin (k+1))-b (⟨j,by omega⟩ : Fin (k+1)))
      simp only [zero_add] at happ
      change segment E 0 (b (⟨j,by omega⟩ : Fin (k+1))) *
        segment E (b (⟨j,by omega⟩ : Fin (k+1)))
          (b (⟨j+1,by omega⟩ : Fin (k+1))-b (⟨j,by omega⟩ : Fin (k+1))) = _
      rw [← happ]
      congr 1
      change b (⟨j,by omega⟩ : Fin (k+1)) +
        (b (⟨j+1,by omega⟩ : Fin (k+1))-b (⟨j,by omega⟩ : Fin (k+1))) = _
      omega
  have he (i : Fin k) : cumulative f (i.val+1) = segment E 0 (b i.succ) := hc _ (by omega)
  simpa only [he] using cumulative_injective k f hf

theorem separatedPrefixes_injective (E : ℕ → ℤ) (hE : ∀ j, E j ≠ 0)
    (hiE : Function.Injective E) (k : ℕ) (r : Fin k → ℕ)
    (hr : ∀ i j : Fin k, i < j → r i + 2 ≤ r j) :
    Function.Injective (FreeGroup.lift (fun i : Fin k => segment E 0 (r i+2))) := by
  let b : Fin (k+1) → ℕ := Fin.cases 0 (fun i => r i+2)
  have hb0 : b 0 = 0 := rfl
  have hb (i : Fin k) : b i.castSucc+2 ≤ b i.succ := by
    change b i.castSucc+2 ≤ r i+2
    by_cases hi : i.val = 0
    · have he : i.castSucc = 0 := Fin.ext hi
      rw [he,hb0]
      omega
    · let j : Fin k := ⟨i.val-1,by have := i.is_lt; omega⟩
      have hji : j < i := by change i.val-1 < i.val; omega
      have he : i.castSucc = j.succ := Fin.ext (by dsimp [j]; omega)
      rw [he]
      have hg := hr j i hji
      change (r j+2)+2 ≤ r i+2
      omega
  simpa only [b,Fin.cases_succ] using boundaryPrefixes_injective E hE hiE k b hb0 hb

def runExponent (B j : ℕ) : ℤ := ((B : ℤ)-1)*(B : ℤ)^j

theorem runExponent_pos {B : ℕ} (hB : 2 ≤ B) (j : ℕ) : 0 < runExponent B j := by
  have hb : (1 : ℤ) < B := by exact_mod_cast hB
  unfold runExponent
  positivity

theorem runExponent_strictMono {B : ℕ} (hB : 2 ≤ B) : StrictMono (runExponent B) := by
  apply strictMono_nat_of_lt_succ
  intro j
  have hp := runExponent_pos hB j
  have hb : (1 : ℤ) < B := by exact_mod_cast hB
  have he : runExponent B (j+1) = runExponent B j * B := by simp [runExponent,pow_succ,mul_assoc]
  rw [he]
  nlinarith

theorem separatedSetPrefixes_injective (E : ℕ → ℤ) (hE : ∀ j, E j ≠ 0)
    (hiE : Function.Injective E) {m : ℕ} (s : Finset (Fin m))
    (hs : ∀ i ∈ s, ∀ j ∈ s, i.val+1 ≠ j.val) :
    Function.Injective (FreeGroup.lift (fun i : s => segment E 0 (i.val.val+2))) := by
  classical
  let e : Fin s.card ≃o s := s.orderIsoOfFin rfl
  have hr (i j : Fin s.card) (hij : i < j) : (e i).val.val+2 ≤ (e j).val.val := by
    have hlt : (e i).val < (e j).val := e.strictMono hij
    have hne := hs (e i).val (e i).property (e j).val (e j).property
    change (e i).val.val < (e j).val.val at hlt
    omega
  have hf := separatedPrefixes_injective E hE hiE s.card (fun i => (e i).val.val) hr
  have he : (FreeGroup.lift (fun i : Fin s.card => segment E 0 ((e i).val.val+2))).comp
      (FreeGroup.map e.symm) = FreeGroup.lift (fun i : s => segment E 0 (i.val.val+2)) := by
    ext i
    simp
  rw [← he]
  exact hf.comp (FreeGroup.map_injective e.symm.injective)

theorem mk_eq_one_of_restricted_lift {ι : Type uι} {G : Type uG} [Group G]
    (f : ι → G) (s : Finset ι)
    (hf : Function.Injective (FreeGroup.lift (fun i : s => f i.val)))
    (L : List (ι × Bool)) (hL : ∀ p ∈ L, p.1 ∈ s)
    (he : FreeGroup.lift f (FreeGroup.mk L) = 1) : FreeGroup.mk L = 1 := by
  classical
  by_cases hs : s.Nonempty
  · let z : s := ⟨hs.choose,hs.choose_spec⟩
    let r (i : ι) : s := if h : i ∈ s then ⟨i,h⟩ else z
    have hr (i : ι) (hi : i ∈ s) : (r i).val = i := by simp [r,hi]
    let R := (FreeGroup.map r) (FreeGroup.mk L)
    have hR : FreeGroup.map (fun i : s => i.val) R = FreeGroup.mk L := by
      simp only [R,FreeGroup.map.mk,List.map_map]
      congr 1
      have hmap : L.map ((fun x : s × Bool => (x.1.val,x.2)) ∘
          (fun x : ι × Bool => (r x.1,x.2))) = L.map id := by
        apply List.map_congr_left
        intro p hp
        exact Prod.ext (hr p.1 (hL p hp)) rfl
      exact hmap.trans (List.map_id L)
    have hh : (FreeGroup.lift f).comp (FreeGroup.map (fun i : s => i.val)) =
        FreeGroup.lift (fun i : s => f i.val) := by ext i; simp
    have heR : FreeGroup.lift (fun i : s => f i.val) R = 1 := by
      rw [← hh, MonoidHom.comp_apply,hR,he]
    have hR1 : R = 1 := hf (heR.trans (map_one _).symm)
    rw [← hR,hR1,map_one]
  · have hnil : L = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro p hp
      exact hs ⟨p.1,hL p hp⟩
    subst L
    rfl

theorem prefixRelation_of_separated {m : ℕ} (E : ℕ → ℤ) (hE : ∀ j, E j ≠ 0)
    (hiE : Function.Injective E) (L : List (Fin m × Bool))
    (hsep : ∀ p ∈ L, ∀ q ∈ L, p.1.val+1 ≠ q.1.val)
    (he : FreeGroup.lift (fun i : Fin m => segment E 0 (i.val+2)) (FreeGroup.mk L) = 1) :
    FreeGroup.mk L = 1 := by
  classical
  let s := (L.map Prod.fst).toFinset
  have hs : ∀ i ∈ s, ∀ j ∈ s, i.val+1 ≠ j.val := by
    intro i hi j hj
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hi)
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hj)
    exact hsep p hp q hq
  apply mk_eq_one_of_restricted_lift _ s (separatedSetPrefixes_injective E hE hiE s hs) L _ he
  intro p hp
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨p,hp,rfl⟩)

end RankTwo

end

end FreeGroupFactorMain

end OAI
end

section
namespace OAI

noncomputable section

universe uG uI uJ uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

attribute [local instance] Classical.propDecidable

namespace FreeGroupFactorMain
namespace RankTwo

section

theorem top_power_dominates (B L k : ℕ) (hB : L < B) (hk : 0 < k) :
    (L : ℤ) * (B : ℤ)^(k-1) < (B : ℤ)^k := by
  have hb : (0 : ℤ) < B := by omega
  have hp : (0 : ℤ) < (B : ℤ)^(k-1) := pow_pos hb _
  calc
    _ < (B : ℤ) * (B : ℤ)^(k-1) := mul_lt_mul_of_pos_right (by exact_mod_cast hB) hp
    _ = (B : ℤ)^k := by rw [mul_comm, ← pow_succ]; congr 1; omega

theorem power_sum_ne_zero {m B L : ℕ} (hB : m * L < B)
    (c : Fin m → ℤ) (hc : ∀ i, |c i| ≤ L) (hne : ∃ i, c i ≠ 0) :
    ∑ i, c i * (B : ℤ)^i.val ≠ 0 := by
  classical
  let s : Finset (Fin m) := Finset.univ.filter (fun i => c i ≠ 0)
  have hs : s.Nonempty := by obtain ⟨i,hi⟩ := hne; exact ⟨i,by simp [s,hi]⟩
  let j := s.max' hs
  have hj : c j ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem s hs)).2
  have hm : 0 < m := by obtain ⟨i,_⟩ := hne; exact lt_of_le_of_lt (Nat.zero_le i.val) i.is_lt
  have hL : 0 < L := by
    obtain ⟨i,hi⟩ := hne
    have hci := hc i
    have : 1 ≤ |c i| := by have := abs_pos.mpr hi; omega
    omega
  have hb : (0 : ℤ) < B := by
    have : 0 < m * L := Nat.mul_pos hm hL
    omega
  have hvan (i : Fin m) (hij : j < i) : c i = 0 := by
    by_contra hi
    have him : i ∈ s := by simp [s,hi]
    exact (not_lt_of_ge (Finset.le_max' s i him)) hij
  have hsplit : (∑ i, c i * (B : ℤ)^i.val) =
      c j * (B : ℤ)^j.val + ∑ i ∈ Finset.univ.erase j, c i * (B : ℤ)^i.val := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
  rw [hsplit]
  by_cases hj0 : j.val = 0
  · have hrest : ∑ i ∈ Finset.univ.erase j, c i * (B : ℤ)^i.val = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hij : j < i := by
        have hine := (Finset.mem_erase.mp hi).1
        have hiv : i.val ≠ j.val := fun h => hine (Fin.ext h)
        change j.val < i.val
        omega
      rw [hvan i hij,zero_mul]
    simpa [hrest,hj0] using hj
  · have hrest : |∑ i ∈ Finset.univ.erase j, c i * (B : ℤ)^i.val| ≤
        (m : ℤ) * L * (B : ℤ)^(j.val-1) := by
      calc
        _ ≤ ∑ i ∈ Finset.univ.erase j, |c i * (B : ℤ)^i.val| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i ∈ Finset.univ.erase j, (L : ℤ) * (B : ℤ)^(j.val-1) := by
          apply Finset.sum_le_sum
          intro i hi
          by_cases hij : i < j
          · rw [abs_mul,abs_of_nonneg (pow_nonneg hb.le _)]
            gcongr
            · exact hc i
            · exact_mod_cast (by omega : i.val ≤ j.val-1)
          · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij)
                (by exact (Finset.mem_erase.mp hi).1.symm)
            rw [hvan i hji,zero_mul,abs_zero]
            positivity
        _ ≤ (m : ℤ) * L * (B : ℤ)^(j.val-1) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          have hcard : ((Finset.univ.erase j).card : ℤ) ≤ m := by
            exact_mod_cast (show (Finset.univ.erase j).card ≤ m by simp only [Finset.card_erase_of_mem (Finset.mem_univ j),Finset.card_univ,Fintype.card_fin]; omega)
          have hn : 0 ≤ (L : ℤ) * (B : ℤ)^(j.val-1) := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hcard hn]
    have hdom : (m : ℤ) * L * (B : ℤ)^(j.val-1) < (B : ℤ)^j.val := by
      simpa [Nat.cast_mul] using top_power_dominates B (m*L) j.val hB (Nat.pos_of_ne_zero hj0)
    have hlead : (B : ℤ)^j.val ≤ |c j * (B : ℤ)^j.val| := by
      rw [abs_mul,abs_of_nonneg (pow_nonneg hb.le _)]
      have hci : 1 ≤ |c j| := by have := abs_pos.mpr hj; omega
      nlinarith [pow_nonneg hb.le j.val]
    intro heq
    have habs : |c j * (B : ℤ)^j.val| =
        |∑ i ∈ Finset.univ.erase j, c i * (B : ℤ)^i.val| := by
      have := eq_neg_of_add_eq_zero_left heq
      rw [this,abs_neg]
    omega

def bExponentHom : SyllableGroup →* Multiplicative ℤ :=
  Monoid.CoprodI.lift (fun i => if i then 1 else MonoidHom.id _)

def bExponent (g : SyllableGroup) : ℤ := Multiplicative.toAdd (bExponentHom g)

@[simp] theorem bExponent_one : bExponent 1 = 0 := by simp [bExponent]
@[simp] theorem bExponent_mul (g h : SyllableGroup) : bExponent (g*h) = bExponent g+bExponent h := by
  simp [bExponent]
@[simp] theorem bExponent_inv (g : SyllableGroup) : bExponent g⁻¹ = -bExponent g := by
  simp [bExponent]
@[simp] theorem bExponent_a (z : ℤ) : bExponent (syllable true z) = 0 := by
  simp [bExponent,bExponentHom,syllable]
@[simp] theorem bExponent_b (z : ℤ) : bExponent (syllable false z) = z := by
  simp [bExponent,bExponentHom,syllable]
@[simp] theorem bExponent_piece (E : ℕ → ℤ) (j : ℕ) : bExponent (piece E j) = E j := by
  simp [piece]

theorem bExponent_segment (B k : ℕ) :
    bExponent (segment (runExponent B) 0 k) = (B : ℤ)^k-1 := by
  induction k with
  | zero => simp
  | succ k ih => simp only [segment_succ,bExponent_mul,bExponent_piece,zero_add,ih]
                 simp only [runExponent,pow_succ]
                 ring

def boolSign (b : Bool) : ℤ := if b then 1 else -1

@[simp] theorem boolSign_true : boolSign true = 1 := rfl
@[simp] theorem boolSign_false : boolSign false = -1 := rfl
@[simp] theorem boolSign_not (b : Bool) : boolSign (!b) = -boolSign b := by cases b <;> rfl
@[simp] theorem abs_boolSign (b : Bool) : |boolSign b| = 1 := by cases b <;> norm_num [boolSign]

def labelCoefficient {I : Type uI} [Fintype I] {m : ℕ}
    (b : I → Bool) (x : I → Fin m) (j : Fin m) : ℤ :=
  ∑ i, if x i = j then boolSign (b i) else 0

theorem labelCoefficient_abs_le {I : Type uI} [Fintype I] {m : ℕ}
    (b : I → Bool) (x : I → Fin m) (j : Fin m) :
    |labelCoefficient b x j| ≤ Fintype.card I := by
  classical
  unfold labelCoefficient
  calc
    _ ≤ ∑ i, |if x i = j then boolSign (b i) else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : I, (1 : ℤ) := by apply Finset.sum_le_sum; intro i _; split_ifs <;> simp
    _ = _ := by simp

theorem labelCoefficient_sum_mul {I : Type uI} [Fintype I] {m : ℕ}
    (b : I → Bool) (x : I → Fin m) (f : Fin m → ℤ) :
    ∑ j, labelCoefficient b x j * f j = ∑ i, boolSign (b i)*f (x i) := by
  classical
  simp only [labelCoefficient,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [ite_mul]

theorem labelCoefficient_eq_zero {I : Type uI} [Fintype I] {m B : ℕ}
    (hB : m * Fintype.card I < B) (hb : 2 ≤ B)
    (b : I → Bool) (x : I → Fin m)
    (hcharge : ∑ i, boolSign (b i) = 0)
    (hexp : ∑ i, boolSign (b i)*((B : ℤ)^((x i).val+2)-1) = 0) :
    ∀ j, labelCoefficient b x j = 0 := by
  classical
  have hn : (B : ℤ) ≠ 0 := by omega
  have he : ∑ i, boolSign (b i)*(B : ℤ)^(x i).val = 0 := by
    have hh : ∑ i, boolSign (b i)*((B : ℤ)^((x i).val+2)-1) =
        (∑ i, boolSign (b i)*(B : ℤ)^(x i).val)*(B : ℤ)^2 - ∑ i, boolSign (b i) := by
      simp only [pow_add,mul_sub,mul_one,Finset.sum_sub_distrib,Finset.sum_mul,mul_assoc]
    rw [hh,hcharge,sub_zero] at hexp
    exact (mul_eq_zero.mp hexp).resolve_right (pow_ne_zero _ hn)
  intro j
  by_contra hj
  have hne := power_sum_ne_zero hB (labelCoefficient b x) (labelCoefficient_abs_le b x) ⟨j,hj⟩
  apply hne
  rw [labelCoefficient_sum_mul]
  exact he

def AdjacentValues {m r : ℕ} (p : Fin r → Fin m) : Prop :=
  ∃ i j, (p i).val + 1 = (p j).val

def Covers {m r : ℕ} (p q : Fin r → Fin m) : Prop := ∀ i, ∃ j, p j = q i

theorem covers_iff {m r : ℕ} (p q : Fin r → Fin m) :
    Covers p q ↔ ∃ σ : Fin r → Fin r, q = p ∘ σ := by
  classical
  constructor
  · intro h
    choose σ hσ using h
    exact ⟨σ,funext (fun i => (hσ i).symm)⟩
  · rintro ⟨σ,rfl⟩ i
    exact ⟨σ i,rfl⟩

def adjacentPairs (m r : ℕ) (i j : Fin r) : Finset (Fin r → Fin m) :=
  Finset.univ.filter (fun p => (p i).val+1 = (p j).val)

theorem card_adjacentPairs_le (m r : ℕ) (i j : Fin r) :
    (adjacentPairs m r i j).card ≤ m^(r-1) := by
  classical
  by_cases hij : i = j
  · subst j
    simp [adjacentPairs]
  · let restrict : {p // p ∈ adjacentPairs m r i j} → ({x : Fin r // x ≠ j} → Fin m) :=
      fun p x => p.val x.val
    have hinj : Function.Injective restrict := by
      intro p q hpq
      apply Subtype.ext
      funext x
      by_cases hx : x = j
      · subst x
        have hpi := (Finset.mem_filter.mp p.property).2
        have hqi := (Finset.mem_filter.mp q.property).2
        have hei : p.val i = q.val i := congrFun hpq ⟨i,hij⟩
        apply Fin.ext
        omega
      · exact congrFun hpq ⟨x,hx⟩
    have hc := Fintype.card_le_of_injective restrict hinj
    have hj : Fintype.card {x : Fin r // x ≠ j} = r-1 := by
      simp [Fintype.card_subtype_compl]
    simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin,hj] using hc

def adjacentFunctions (m r : ℕ) : Finset (Fin r → Fin m) := by
  classical
  exact Finset.univ.filter AdjacentValues

theorem adjacentFunctions_eq (m r : ℕ) :
    adjacentFunctions m r = Finset.univ.biUnion (fun i : Fin r =>
      Finset.univ.biUnion (fun j : Fin r => adjacentPairs m r i j)) := by
  classical
  ext p
  simp [adjacentFunctions,AdjacentValues,adjacentPairs]

theorem card_adjacentFunctions_le (m r : ℕ) :
    (adjacentFunctions m r).card ≤ r^2 * m^(r-1) := by
  classical
  rw [adjacentFunctions_eq]
  calc
    _ ≤ ∑ i : Fin r, (Finset.univ.biUnion (fun j : Fin r => adjacentPairs m r i j)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ i : Fin r, ∑ j : Fin r, (adjacentPairs m r i j).card :=
      Finset.sum_le_sum (fun _ _ => Finset.card_biUnion_le)
    _ ≤ ∑ _i : Fin r, ∑ _j : Fin r, m^(r-1) := by
      gcongr with i _ j _
      exact card_adjacentPairs_le m r i j
    _ = _ := by simp [pow_two,Nat.mul_assoc]

def coveredPairs (m r : ℕ) : Finset ((Fin r → Fin m) × (Fin r → Fin m)) := by
  classical
  exact Finset.univ.filter (fun p => Covers p.1 p.2)

def badCoveredPairs (m r : ℕ) : Finset ((Fin r → Fin m) × (Fin r → Fin m)) := by
  classical
  exact Finset.univ.filter (fun p => Covers p.1 p.2 ∧ AdjacentValues p.1)

theorem coveredPairs_param (m r : ℕ) :
    coveredPairs m r = Finset.univ.image (fun t : (Fin r → Fin m) × (Fin r → Fin r) =>
      (t.1,t.1 ∘ t.2)) := by
  classical
  ext ⟨p,q⟩
  constructor
  · intro h
    obtain ⟨σ,hσ⟩ := (covers_iff p q).mp (Finset.mem_filter.mp h).2
    apply Finset.mem_image.mpr
    exact ⟨(p,σ),Finset.mem_univ _,Prod.ext rfl hσ.symm⟩
  · intro h
    obtain ⟨⟨p',σ⟩,_,he⟩ := Finset.mem_image.mp h
    have hp : p' = p := congrArg Prod.fst he
    have hq : p' ∘ σ = q := congrArg Prod.snd he
    subst p'
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(covers_iff p q).mpr ⟨σ,hq.symm⟩⟩

theorem card_coveredPairs_le (m r : ℕ) :
    (coveredPairs m r).card ≤ m^r * r^r := by
  classical
  rw [coveredPairs_param]
  simpa using Finset.card_image_le (s := (Finset.univ : Finset ((Fin r → Fin m) × (Fin r → Fin r))))
    (f := fun t => (t.1,t.1 ∘ t.2))

theorem badCoveredPairs_param (m r : ℕ) :
    badCoveredPairs m r = ((adjacentFunctions m r) ×ˢ (Finset.univ : Finset (Fin r → Fin r))).image
      (fun t => (t.1,t.1 ∘ t.2)) := by
  classical
  ext ⟨p,q⟩
  constructor
  · intro h
    obtain ⟨hc,ha⟩ := (Finset.mem_filter.mp h).2
    obtain ⟨σ,hσ⟩ := (covers_iff p q).mp hc
    apply Finset.mem_image.mpr
    refine ⟨(p,σ),?_,Prod.ext rfl hσ.symm⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩,Finset.mem_univ _⟩
  · intro h
    obtain ⟨⟨p',σ⟩,hm,he⟩ := Finset.mem_image.mp h
    have hp : p' = p := congrArg Prod.fst he
    have hq : p' ∘ σ = q := congrArg Prod.snd he
    subst p'
    have ha := (Finset.mem_filter.mp (Finset.mem_product.mp hm).1).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(covers_iff p q).mpr ⟨σ,hq.symm⟩,ha⟩

theorem card_badCoveredPairs_le (m r : ℕ) :
    (badCoveredPairs m r).card ≤ (r^2 * r^r) * m^(r-1) := by
  classical
  rw [badCoveredPairs_param]
  calc
    _ ≤ ((adjacentFunctions m r) ×ˢ (Finset.univ : Finset (Fin r → Fin r))).card := Finset.card_image_le
    _ = (adjacentFunctions m r).card * r^r := by simp
    _ ≤ (r^2 * m^(r-1)) * r^r := Nat.mul_le_mul_right _ (card_adjacentFunctions_le m r)
    _ = _ := by ring

variable {I : Type uI}

def coloredEncode {m r : ℕ} (b : I → Bool)
    (eP : Fin r ≃ {i // b i = true}) (eN : Fin r ≃ {i // b i = false})
    (x : I → Fin m) : (Fin r → Fin m) × (Fin r → Fin m) :=
  (fun j => x (eP j).val, fun j => x (eN j).val)

theorem coloredEncode_injective {m r : ℕ} (b : I → Bool)
    (eP : Fin r ≃ {i // b i = true}) (eN : Fin r ≃ {i // b i = false}) :
    Function.Injective (coloredEncode (m := m) b eP eN) := by
  intro x y h
  funext i
  cases hi : b i with
  | false =>
    have he := congrFun (congrArg Prod.snd h) (eN.symm ⟨i,hi⟩)
    simpa only [coloredEncode,Equiv.apply_symm_apply] using he
  | true =>
    have he := congrFun (congrArg Prod.fst h) (eP.symm ⟨i,hi⟩)
    simpa only [coloredEncode,Equiv.apply_symm_apply] using he

def ColoredCovers {m : ℕ} (b : I → Bool) (x : I → Fin m) : Prop :=
  ∀ i, b i = false → ∃ j, b j = true ∧ x j = x i

def ColoredAdjacent {m : ℕ} (b : I → Bool) (x : I → Fin m) : Prop :=
  ∃ i j, b i = true ∧ b j = true ∧ (x i).val+1 = (x j).val

theorem coloredEncode_covers {m r : ℕ} (b : I → Bool)
    (eP : Fin r ≃ {i // b i = true}) (eN : Fin r ≃ {i // b i = false})
    (x : I → Fin m) (h : ColoredCovers b x) :
    Covers (coloredEncode b eP eN x).1 (coloredEncode b eP eN x).2 := by
  intro i
  obtain ⟨j,hj,he⟩ := h (eN i).val (eN i).property
  refine ⟨eP.symm ⟨j,hj⟩,?_⟩
  simpa only [coloredEncode,Equiv.apply_symm_apply] using he

theorem coloredEncode_adjacent {m r : ℕ} (b : I → Bool)
    (eP : Fin r ≃ {i // b i = true}) (eN : Fin r ≃ {i // b i = false})
    (x : I → Fin m) (h : ColoredAdjacent b x) :
    AdjacentValues (coloredEncode b eP eN x).1 := by
  obtain ⟨i,j,hi,hj,he⟩ := h
  refine ⟨eP.symm ⟨i,hi⟩,eP.symm ⟨j,hj⟩,?_⟩
  simpa only [coloredEncode,Equiv.apply_symm_apply] using he

theorem card_coloredCovered_le {m r : ℕ} (b : I → Bool)
    (eP : Fin r ≃ {i // b i = true}) (eN : Fin r ≃ {i // b i = false})
    (s : Finset (I → Fin m)) (hs : ∀ x ∈ s, ColoredCovers b x) :
    s.card ≤ m^r * r^r := by
  classical
  have he : s.image (coloredEncode b eP eN) ⊆ coveredPairs m r := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,coloredEncode_covers b eP eN x (hs x hx)⟩
  calc
    _ = (s.image (coloredEncode b eP eN)).card := (Finset.card_image_of_injective s (coloredEncode_injective b eP eN)).symm
    _ ≤ (coveredPairs m r).card := Finset.card_le_card he
    _ ≤ _ := card_coveredPairs_le m r

theorem card_coloredBad_le {m r : ℕ} (b : I → Bool)
    (eP : Fin r ≃ {i // b i = true}) (eN : Fin r ≃ {i // b i = false})
    (s : Finset (I → Fin m))
    (hs : ∀ x ∈ s, ColoredCovers b x ∧ ColoredAdjacent b x) :
    s.card ≤ (r^2 * r^r) * m^(r-1) := by
  classical
  have he : s.image (coloredEncode b eP eN) ⊆ badCoveredPairs m r := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hc,ha⟩ := hs x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,coloredEncode_covers b eP eN x hc,
      coloredEncode_adjacent b eP eN x ha⟩
  calc
    _ = (s.image (coloredEncode b eP eN)).card := (Finset.card_image_of_injective s (coloredEncode_injective b eP eN)).symm
    _ ≤ (badCoveredPairs m r).card := Finset.card_le_card he
    _ ≤ _ := card_badCoveredPairs_le m r

end

def prefixHom (B m : ℕ) : FreeGroup (Fin m) →* SyllableGroup :=
  FreeGroup.lift (fun i => segment (runExponent B) 0 (i.val+2))

def patternWord {m l : ℕ} (b : Fin l → Bool) (x : Fin l → Fin m) : FreeGroup (Fin m) :=
  FreeGroup.mk (List.ofFn (fun i => (x i,b i)))

def pairColors {I : Type uI} {J : Type uJ} (b : I → Bool) (c : J → Bool) : I ⊕ J → Bool :=
  Sum.elim b (fun j => !(c j))

def pairLabels {I : Type uI} {J : Type uJ} {m : ℕ} (x : I → Fin m) (y : J → Fin m) : I ⊕ J → Fin m :=
  Sum.elim x y

theorem pairLabels_injective {I : Type uI} {J : Type uJ} {m : ℕ} :
    Function.Injective (fun p : (I → Fin m) × (J → Fin m) => pairLabels p.1 p.2) := by
  intro p q h
  apply Prod.ext
  · funext i; exact congrFun h (.inl i)
  · funext j; exact congrFun h (.inr j)

theorem bExponent_lift_mk {ι : Type uι} (f : ι → SyllableGroup) (L : List (ι × Bool)) :
    bExponent (FreeGroup.lift f (FreeGroup.mk L)) =
      (L.map (fun p => boolSign p.2 * bExponent (f p.1))).sum := by
  rw [FreeGroup.lift_mk]
  induction L with
  | nil => simp
  | cons p L ih =>
    cases p with | mk i b => cases b <;> simp [ih]

theorem bExponent_pattern (B m l : ℕ) (b : Fin l → Bool) (x : Fin l → Fin m) :
    bExponent (prefixHom B m (patternWord b x)) =
      ∑ i, boolSign (b i) * ((B : ℤ)^((x i).val+2)-1) := by
  unfold prefixHom patternWord
  rw [bExponent_lift_mk,List.map_ofFn,List.sum_ofFn]
  simp only [bExponent_segment]
  rfl

theorem covers_of_balanced {I : Type uI} [Fintype I] {m : ℕ}
    (b : I → Bool) (x : I → Fin m) (he : ∀ j, labelCoefficient b x j = 0) :
    ColoredCovers b x := by
  classical
  intro i hi
  by_contra hn
  have hno (j : I) (hj : x j = x i) : b j = false := by
    cases hb : b j with
    | false => rfl
    | true => exact False.elim (hn ⟨j,hb,hj⟩)
  have hle (j : I) : (if x j = x i then boolSign (b j) else 0 : ℤ) ≤ 0 := by
    split_ifs with hj
    · rw [hno j hj]; norm_num
    · rfl
  have hlt : (∑ j, if x j = x i then boolSign (b j) else 0 : ℤ) < ∑ _j : I, 0 := by
    apply Finset.sum_lt_sum (fun j _ => hle j)
    exact ⟨i,Finset.mem_univ _,by simp [hi]⟩
  have hz := he (x i)
  simp only [labelCoefficient] at hz
  simp only [Finset.sum_const_zero] at hlt
  omega

theorem collision_covers {m l k B : ℕ} (hB : m * (l+k) < B) (hb : 2 ≤ B)
    (b : Fin l → Bool) (c : Fin k → Bool) (x : Fin l → Fin m) (y : Fin k → Fin m)
    (hc : ∑ i, boolSign (b i) = ∑ j, boolSign (c j))
    (he : prefixHom B m (patternWord b x) = prefixHom B m (patternWord c y)) :
    ColoredCovers (pairColors b c) (pairLabels x y) := by
  have he' := congrArg bExponent he
  rw [bExponent_pattern,bExponent_pattern] at he'
  have hcharge : ∑ i, boolSign (pairColors b c i) = 0 := by
    simp only [Fintype.sum_sum_type,pairColors,Sum.elim_inl,Sum.elim_inr,boolSign_not,
      Finset.sum_neg_distrib,hc,add_neg_cancel]
  have hexp : ∑ i, boolSign (pairColors b c i)*((B : ℤ)^((pairLabels x y i).val+2)-1) = 0 := by
    simp only [Fintype.sum_sum_type,pairColors,pairLabels,Sum.elim_inl,Sum.elim_inr,
      boolSign_not,neg_mul,Finset.sum_neg_distrib,he',add_neg_cancel]
  apply covers_of_balanced
  apply labelCoefficient_eq_zero (by simpa only [Fintype.card_sum,Fintype.card_fin] using hB) hb _ _ hcharge hexp

theorem separated_of_covers {I : Type uI} {m : ℕ} (b : I → Bool) (x : I → Fin m)
    (hc : ColoredCovers b x) (ha : ¬ColoredAdjacent b x) :
    ∀ i j, (x i).val+1 ≠ (x j).val := by
  have hp (i : I) : ∃ j, b j = true ∧ x j = x i := by
    cases hi : b i with
    | false => exact hc i hi
    | true => exact ⟨i,hi,rfl⟩
  intro i j he
  obtain ⟨u,hu,heu⟩ := hp i
  obtain ⟨v,hv,hev⟩ := hp j
  exact ha ⟨u,v,hu,hv,by simpa only [heu,hev] using he⟩

theorem collision_free_of_separated {m l k B : ℕ} (hb : 2 ≤ B)
    (b : Fin l → Bool) (c : Fin k → Bool) (x : Fin l → Fin m) (y : Fin k → Fin m)
    (hs : ∀ i j, (pairLabels x y i).val+1 ≠ (pairLabels x y j).val)
    (he : prefixHom B m (patternWord b x) = prefixHom B m (patternWord c y)) :
    patternWord b x = patternWord c y := by
  let L := List.ofFn (fun i => (x i,b i)) ++ FreeGroup.invRev (List.ofFn (fun j => (y j,c j)))
  have hlabel (p : Fin m × Bool) (hp : p ∈ L) : ∃ i, pairLabels x y i = p.1 := by
    simp only [L,List.mem_append,FreeGroup.invRev,List.mem_reverse,List.mem_map,List.mem_ofFn] at hp
    rcases hp with h | ⟨q,⟨j,hj⟩,hq⟩
    · obtain ⟨i,hi⟩ := h
      exact ⟨.inl i,congrArg Prod.fst hi⟩
    · subst q
      exact ⟨.inr j,congrArg Prod.fst hq⟩
  have hsep : ∀ p ∈ L, ∀ q ∈ L, p.1.val+1 ≠ q.1.val := by
    intro p hp q hq
    obtain ⟨i,hi⟩ := hlabel p hp
    obtain ⟨j,hj⟩ := hlabel q hq
    simpa only [hi,hj] using hs i j
  have hmk : FreeGroup.mk L = patternWord b x * (patternWord c y)⁻¹ := by
    rw [patternWord,patternWord,FreeGroup.inv_mk,FreeGroup.mul_mk]
  have hrel : prefixHom B m (FreeGroup.mk L) = 1 := by
    rw [hmk,map_mul,map_inv,he,mul_inv_cancel]
  have hzero := prefixRelation_of_separated (runExponent B)
    (fun j => ne_of_gt (runExponent_pos hb j)) (runExponent_strictMono hb).injective L hsep hrel
  rw [hmk,mul_inv_eq_one] at hzero
  exact hzero

theorem collision_bad_adjacent {m l k B : ℕ} (hB : m * (l+k) < B) (hb : 2 ≤ B)
    (b : Fin l → Bool) (c : Fin k → Bool) (x : Fin l → Fin m) (y : Fin k → Fin m)
    (hc : ∑ i, boolSign (b i) = ∑ j, boolSign (c j))
    (he : prefixHom B m (patternWord b x) = prefixHom B m (patternWord c y))
    (hne : patternWord b x ≠ patternWord c y) :
    ColoredCovers (pairColors b c) (pairLabels x y) ∧
      ColoredAdjacent (pairColors b c) (pairLabels x y) := by
  have hc' := collision_covers hB hb b c x y hc he
  refine ⟨hc',?_⟩
  by_contra ha
  exact hne (collision_free_of_separated hb b c x y (separated_of_covers _ _ hc' ha) he)

theorem card_patternCollisions_le {m l k B r : ℕ} (hB : m*(l+k) < B) (hb : 2 ≤ B)
    (b : Fin l → Bool) (c : Fin k → Bool)
    (eP : Fin r ≃ {i // pairColors b c i = true})
    (eN : Fin r ≃ {i // pairColors b c i = false})
    (hc : ∑ i, boolSign (b i) = ∑ j, boolSign (c j))
    (s : Finset ((Fin l → Fin m) × (Fin k → Fin m)))
    (hs : ∀ p ∈ s, prefixHom B m (patternWord b p.1) = prefixHom B m (patternWord c p.2)) :
    s.card ≤ m^r * r^r := by
  classical
  let t := s.image (fun p => pairLabels p.1 p.2)
  have ht : ∀ x ∈ t, ColoredCovers (pairColors b c) x := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    exact collision_covers hB hb b c p.1 p.2 hc (hs p hp)
  have hh := card_coloredCovered_le (pairColors b c) eP eN t ht
  rwa [Finset.card_image_of_injective s pairLabels_injective] at hh

theorem card_patternBadCollisions_le {m l k B r : ℕ} (hB : m*(l+k) < B) (hb : 2 ≤ B)
    (b : Fin l → Bool) (c : Fin k → Bool)
    (eP : Fin r ≃ {i // pairColors b c i = true})
    (eN : Fin r ≃ {i // pairColors b c i = false})
    (hc : ∑ i, boolSign (b i) = ∑ j, boolSign (c j))
    (s : Finset ((Fin l → Fin m) × (Fin k → Fin m)))
    (hs : ∀ p ∈ s, prefixHom B m (patternWord b p.1) = prefixHom B m (patternWord c p.2) ∧
      patternWord b p.1 ≠ patternWord c p.2) :
    s.card ≤ (r^2*r^r)*m^(r-1) := by
  classical
  let t := s.image (fun p => pairLabels p.1 p.2)
  have ht : ∀ x ∈ t, ColoredCovers (pairColors b c) x ∧ ColoredAdjacent (pairColors b c) x := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    exact collision_bad_adjacent hB hb b c p.1 p.2 hc (hs p hp).1 (hs p hp).2
  have hh := card_coloredBad_le (pairColors b c) eP eN t ht
  rwa [Finset.card_image_of_injective s pairLabels_injective] at hh

theorem card_patternCollisions_le_free_add {m l k B r : ℕ} (hB : m*(l+k) < B) (hb : 2 ≤ B)
    (b : Fin l → Bool) (c : Fin k → Bool)
    (eP : Fin r ≃ {i // pairColors b c i = true})
    (eN : Fin r ≃ {i // pairColors b c i = false})
    (hc : ∑ i, boolSign (b i) = ∑ j, boolSign (c j))
    (s : Finset ((Fin l → Fin m) × (Fin k → Fin m))) :
    (s.filter (fun p => prefixHom B m (patternWord b p.1) = prefixHom B m (patternWord c p.2))).card ≤
      (s.filter (fun p => patternWord b p.1 = patternWord c p.2)).card + (r^2*r^r)*m^(r-1) := by
  classical
  let t := s.filter (fun p => prefixHom B m (patternWord b p.1) = prefixHom B m (patternWord c p.2))
  let u := t.filter (fun p => patternWord b p.1 = patternWord c p.2)
  let v := t.filter (fun p => ¬ patternWord b p.1 = patternWord c p.2)
  have huc : u.card ≤ (s.filter (fun p => patternWord b p.1 = patternWord c p.2)).card := by
    apply Finset.card_le_card
    intro p hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1,
      (Finset.mem_filter.mp hp).2⟩
  have hvc : v.card ≤ (r^2*r^r)*m^(r-1) := by
    apply card_patternBadCollisions_le hB hb b c eP eN hc v
    intro p hp
    exact ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2,(Finset.mem_filter.mp hp).2⟩
  have he : u.card+v.card = t.card := Finset.card_filter_add_card_filter_not _
  change t.card ≤ _
  omega

def alternating (b : Bool) : (l : ℕ) → Fin l → Bool
  | 0 => Fin.elim0
  | l+1 => Fin.cases b (alternating (!b) l)

@[simp] theorem alternating_zero (b : Bool) (l : ℕ) : alternating b (l+1) 0 = b := rfl
@[simp] theorem alternating_succ (b : Bool) (l : ℕ) (i : Fin l) :
    alternating b (l+1) i.succ = alternating (!b) l i := rfl

theorem signed_ofFn {ι : Type uι} (b : Bool) (l : ℕ) (x : Fin l → ι) :
    Radial.signed b (List.ofFn x) = List.ofFn (fun i => (x i,alternating b l i)) := by
  induction l generalizing b with
  | zero => simp [Radial.signed]
  | succ l ih =>
    rw [List.ofFn_succ,Radial.signed,ih,List.ofFn_succ]
    rfl

theorem vertex_ofFn {m l : ℕ} (b : Bool) (x : Fin l → Fin m) :
    Radial.vertex b (List.ofFn x) = patternWord (alternating b l) x := by
  unfold Radial.vertex patternWord
  rw [signed_ofFn]

def positiveCount (b : Bool) (l : ℕ) : ℕ := ∑ i, if alternating b l i = true then 1 else 0

@[simp] theorem positiveCount_zero (b : Bool) : positiveCount b 0 = 0 := by simp [positiveCount]
@[simp] theorem positiveCount_succ (b : Bool) (l : ℕ) :
    positiveCount b (l+1) = (if b = true then 1 else 0)+positiveCount (!b) l := by
  simp only [positiveCount,Fin.sum_univ_succ,alternating_zero,alternating_succ]
  rfl

theorem positiveCount_two (b : Bool) (l : ℕ) : positiveCount b (l+2) = 1+positiveCount b l := by
  rw [positiveCount_succ,positiveCount_succ]
  cases b <;> simp

theorem positiveCount_even (b : Bool) (k : ℕ) : positiveCount b (2*k) = k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ,positiveCount_two,ih]; omega

theorem positiveCount_odd (b : Bool) (k : ℕ) :
    positiveCount b (2*k+1) = (if b = true then 1 else 0)+k := by
  rw [positiveCount_succ,positiveCount_even]

theorem card_alternating_pos (b : Bool) (l : ℕ) :
    Fintype.card {i // alternating b l i = true} = positiveCount b l := by
  classical
  rw [Fintype.card_subtype,Finset.card_filter]
  rfl

theorem card_alternating_neg (b : Bool) (l : ℕ) :
    Fintype.card {i // alternating b l i = false} = l-positiveCount b l := by
  classical
  have hh := Fintype.card_subtype_compl (fun i : Fin l => alternating b l i = true)
  simpa only [Bool.not_eq_true,Fintype.card_fin,card_alternating_pos] using hh

theorem alternating_charge (b : Bool) (l : ℕ) :
    (∑ i, boolSign (alternating b l i)) = 2*(positiveCount b l : ℤ)-l := by
  classical
  have hh (i : Fin l) : boolSign (alternating b l i) =
      2*(if alternating b l i = true then (1 : ℤ) else 0)-1 := by
    cases alternating b l i <;> norm_num
  simp only [hh,Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one,positiveCount]
  push_cast
  rfl

theorem card_pairColors_pos {I : Type uI} {J : Type uJ} [Fintype I] [Fintype J]
    (b : I → Bool) (c : J → Bool) :
    Fintype.card {i // pairColors b c i = true} =
      Fintype.card {i // b i = true} + Fintype.card {j // c j = false} := by
  classical
  simp only [Fintype.card_subtype,Finset.card_filter]
  rw [Fintype.sum_sum_type]
  simp only [pairColors,Sum.elim_inl,Sum.elim_inr,Bool.not_eq_true_eq_eq_false]
  rfl

theorem card_pairColors_neg {I : Type uI} {J : Type uJ} [Fintype I] [Fintype J]
    (b : I → Bool) (c : J → Bool) :
    Fintype.card {i // pairColors b c i = false} =
      Fintype.card {i // b i = false} + Fintype.card {j // c j = true} := by
  classical
  simp only [Fintype.card_subtype,Finset.card_filter]
  rw [Fintype.sum_sum_type]
  simp only [pairColors,Sum.elim_inl,Sum.elim_inr,Bool.not_eq_false_eq_eq_true]
  rfl

end RankTwo

def coefficientPair {G : Type uG} (h k : G →₀ ℝ) : ℝ := h.sum (fun g c => c * k g)

@[simp] theorem coefficientPair_self {G : Type uG} (h : G →₀ ℝ) :
    coefficientPair h h = coefficientSqNorm h := by
  unfold coefficientPair coefficientSqNorm
  apply Finsupp.sum_congr
  intro g _
  exact (pow_two (h g)).symm

@[simp] theorem coefficientPair_zero_left {G : Type uG} (k : G →₀ ℝ) : coefficientPair 0 k = 0 := by
  simp [coefficientPair]

@[simp] theorem coefficientPair_single_left {G : Type uG} (g : G) (c : ℝ) (k : G →₀ ℝ) :
    coefficientPair (Finsupp.single g c) k = c * k g := by simp [coefficientPair]

@[simp] theorem coefficientPair_add_left {G : Type uG} (h k l : G →₀ ℝ) :
    coefficientPair (h+k) l = coefficientPair h l + coefficientPair k l := by
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul ..)

@[simp] theorem coefficientPair_sum_left {I : Type uI} {G : Type uG} (s : Finset I) (h : I → G →₀ ℝ) (k : G →₀ ℝ) :
    coefficientPair (∑ i ∈ s, h i) k = ∑ i ∈ s, coefficientPair (h i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi,ih]

@[simp] theorem coefficientPair_zero_right {G : Type uG} (h : G →₀ ℝ) : coefficientPair h 0 = 0 := by
  simp [coefficientPair]

@[simp] theorem coefficientPair_add_right {G : Type uG} (h k l : G →₀ ℝ) :
    coefficientPair h (k+l) = coefficientPair h k + coefficientPair h l := by
  simp [coefficientPair,mul_add,Finsupp.sum_add]

@[simp] theorem coefficientPair_single_right {G : Type uG} (h : G →₀ ℝ) (g : G) (c : ℝ) :
    coefficientPair h (Finsupp.single g c) = h g * c := by
  classical
  simp [coefficientPair,Finsupp.sum,Finsupp.single_apply]
  exact fun h => Or.inl h

@[simp] theorem coefficientPair_sum_right {I : Type uI} {G : Type uG} (s : Finset I) (h : G →₀ ℝ) (k : I → G →₀ ℝ) :
    coefficientPair h (∑ i ∈ s, k i) = ∑ i ∈ s, coefficientPair h (k i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi,ih]

theorem coefficientPair_smul_left {G : Type uG} (c : ℝ) (h k : G →₀ ℝ) :
    coefficientPair (c • h) k = c * coefficientPair h k := by
  unfold coefficientPair
  rw [Finsupp.sum_smul_index (fun _ => zero_mul _)]
  simp only [mul_assoc,Finsupp.mul_sum]

theorem coefficientPair_smul_right {G : Type uG} (c : ℝ) (h k : G →₀ ℝ) :
    coefficientPair h (c • k) = c * coefficientPair h k := by
  unfold coefficientPair
  simp only [Finsupp.smul_apply,smul_eq_mul,Finsupp.mul_sum,mul_left_comm]

theorem coefficientPair_single_sums {I : Type uI} {J : Type uJ} {G : Type uG} (s : Finset I) (t : Finset J)
    (f : I → G) (g : J → G) (a : I → ℝ) (b : J → ℝ) :
    coefficientPair (∑ i ∈ s, Finsupp.single (f i) (a i)) (∑ j ∈ t, Finsupp.single (g j) (b j)) =
      ∑ i ∈ s, ∑ j ∈ t, if f i = g j then a i * b j else 0 := by
  classical
  rw [coefficientPair_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [coefficientPair_sum_right]
  simp only [coefficientPair_single_left,Finsupp.single_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : f i = g j
  · rw [ite_eq_left h.symm,ite_eq_left h]
  · rw [ite_eq_right (Ne.symm h),ite_eq_right h,mul_zero]

theorem coefficientPair_shells {I : Type uI} {J : Type uJ} {G : Type uG} (s : Finset I) (t : Finset J)
    (f : I → G) (g : J → G) :
    coefficientPair (∑ i ∈ s, Finsupp.single (f i) 1) (∑ j ∈ t, Finsupp.single (g j) 1) =
      ((s ×ˢ t).filter (fun p : I × J => f p.1 = g p.2)).card := by
  classical
  rw [coefficientPair_single_sums]
  simp only [mul_one,Finset.card_filter,Finset.sum_product]
  push_cast
  rfl

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uG uH uK uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

attribute [local instance] Classical.propDecidable

namespace FreeGroupFactorMain

namespace RankTwo

def tupleSphere (m l : ℕ) : Finset (Fin l → Fin m) :=
  Finset.univ.filter (fun x => List.ofFn x ∈ Radial.sphere l)

theorem tupleSphere_image (m l : ℕ) :
    (tupleSphere m l).image List.ofFn = Radial.sphere l := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hw
    exact (Finset.mem_filter.mp hx).2
  · intro hw
    have hl := Radial.sphere_mem_length l hw
    subst l
    refine Finset.mem_image.mpr ⟨w.get,?_,List.ofFn_get w⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [List.ofFn_get] using hw⟩

theorem shell_eq_tuple (m l : ℕ) (b : Bool) :
    Radial.shell (ι := Fin m) b l =
      ∑ x ∈ tupleSphere m l, Finsupp.single (patternWord (alternating b l) x) (1 : ℝ) := by
  classical
  unfold Radial.shell
  rw [← tupleSphere_image,Finset.sum_image (fun _ _ _ _ he => List.ofFn_injective he)]
  simp only [vertex_ofFn]

theorem pair_push_pattern_le {m l k B r : ℕ} (hB : m*(l+k) < B) (hb : 2 ≤ B)
    (b : Fin l → Bool) (c : Fin k → Bool)
    (eP : Fin r ≃ {i // pairColors b c i = true})
    (eN : Fin r ≃ {i // pairColors b c i = false})
    (hc : ∑ i, boolSign (b i) = ∑ j, boolSign (c j))
    (s : Finset (Fin l → Fin m)) (t : Finset (Fin k → Fin m)) :
    coefficientPair
        (pushCoefficients (prefixHom B m) (∑ x ∈ s, Finsupp.single (patternWord b x) 1))
        (pushCoefficients (prefixHom B m) (∑ y ∈ t, Finsupp.single (patternWord c y) 1)) ≤
      (m : ℝ)^r * r^r := by
  classical
  simp only [map_sum,pushCoefficients_single]
  rw [coefficientPair_shells]
  have hh := card_patternCollisions_le hB hb b c eP eN hc
    ((s ×ˢ t).filter (fun p => prefixHom B m (patternWord b p.1) = prefixHom B m (patternWord c p.2)))
    (fun p hp => (Finset.mem_filter.mp hp).2)
  convert (Nat.cast_le (α := ℝ)).mpr hh using 1
  all_goals push_cast
  all_goals (first | rfl | congr 4)

theorem pair_push_pattern_le_free_add {m l k B r : ℕ} (hB : m*(l+k) < B) (hb : 2 ≤ B)
    (b : Fin l → Bool) (c : Fin k → Bool)
    (eP : Fin r ≃ {i // pairColors b c i = true})
    (eN : Fin r ≃ {i // pairColors b c i = false})
    (hc : ∑ i, boolSign (b i) = ∑ j, boolSign (c j))
    (s : Finset (Fin l → Fin m)) (t : Finset (Fin k → Fin m)) :
    coefficientPair
        (pushCoefficients (prefixHom B m) (∑ x ∈ s, Finsupp.single (patternWord b x) 1))
        (pushCoefficients (prefixHom B m) (∑ y ∈ t, Finsupp.single (patternWord c y) 1)) ≤
      coefficientPair (∑ x ∈ s, Finsupp.single (patternWord b x) 1)
        (∑ y ∈ t, Finsupp.single (patternWord c y) 1) + (r^2*r^r : ℝ)*m^(r-1) := by
  classical
  simp only [map_sum,pushCoefficients_single]
  rw [coefficientPair_shells,coefficientPair_shells]
  convert (Nat.cast_le (α := ℝ)).mpr (card_patternCollisions_le_free_add hB hb b c eP eN hc (s ×ˢ t)) using 1
  all_goals push_cast
  all_goals (first | rfl | congr 4)

theorem right_pairColors_card (k : ℕ) (d : Bool) :
    Fintype.card {i // pairColors (alternating false (2*k+1)) (alternating false (2*k+1)) i = d} =
      2*k+1 := by
  cases d
  · rw [card_pairColors_neg]
    simp only [card_alternating_pos,card_alternating_neg,positiveCount_odd,Bool.false_eq_true,
      ↓reduceIte,zero_add]
    omega
  · rw [card_pairColors_pos]
    simp only [card_alternating_pos,card_alternating_neg,positiveCount_odd,Bool.false_eq_true,
      ↓reduceIte,zero_add]
    omega

theorem positiveCount_even_add_two (b : Bool) (k : ℕ) : positiveCount b (2*k+2) = k+1 := by
  rw [positiveCount_two,positiveCount_even]
  omega

theorem left_pairColors_card (k l : ℕ) (d : Bool) :
    Fintype.card {i // pairColors (alternating true (2*k+2)) (alternating true (2*l+2)) i = d} =
      k+l+2 := by
  cases d
  · rw [card_pairColors_neg]
    simp only [card_alternating_pos,card_alternating_neg,positiveCount_even_add_two]
    omega
  · rw [card_pairColors_pos]
    simp only [card_alternating_pos,card_alternating_neg,positiveCount_even_add_two]
    omega

theorem pair_shell_right_le {m k B : ℕ} (hB : m*((2*k+1)+(2*k+1)) < B) (hb : 2 ≤ B) :
    coefficientPair (pushCoefficients (prefixHom B m) (Radial.shell false (2*k+1)))
      (pushCoefficients (prefixHom B m) (Radial.shell false (2*k+1))) ≤
      (m : ℝ)^(2*k+1) * (2*k+1 : ℝ)^(2*k+1) := by
  let eP : Fin (2*k+1) ≃ {i // pairColors (alternating false (2*k+1)) (alternating false (2*k+1)) i = true} :=
    (Fintype.equivFinOfCardEq (right_pairColors_card k true)).symm
  let eN : Fin (2*k+1) ≃ {i // pairColors (alternating false (2*k+1)) (alternating false (2*k+1)) i = false} :=
    (Fintype.equivFinOfCardEq (right_pairColors_card k false)).symm
  rw [shell_eq_tuple m _ false]
  convert pair_push_pattern_le hB hb _ _ eP eN rfl (tupleSphere m _) (tupleSphere m _) using 1
  all_goals push_cast
  all_goals rfl

theorem pair_shell_left_le_free_add {m k l B : ℕ} (hB : m*((2*k+2)+(2*l+2)) < B) (hb : 2 ≤ B) :
    coefficientPair (pushCoefficients (prefixHom B m) (Radial.shell true (2*k+2)))
      (pushCoefficients (prefixHom B m) (Radial.shell true (2*l+2))) ≤
      coefficientPair (Radial.shell (ι := Fin m) true (2*k+2)) (Radial.shell true (2*l+2)) +
        ((k+l+2 : ℝ)^2*(k+l+2 : ℝ)^(k+l+2))*(m : ℝ)^(k+l+1) := by
  let eP : Fin (k+l+2) ≃ {i // pairColors (alternating true (2*k+2)) (alternating true (2*l+2)) i = true} :=
    (Fintype.equivFinOfCardEq (left_pairColors_card k l true)).symm
  let eN : Fin (k+l+2) ≃ {i // pairColors (alternating true (2*k+2)) (alternating true (2*l+2)) i = false} :=
    (Fintype.equivFinOfCardEq (left_pairColors_card k l false)).symm
  have hc : ∑ i, boolSign (alternating true (2*k+2) i) = ∑ i, boolSign (alternating true (2*l+2) i) := by
    rw [alternating_charge,alternating_charge,positiveCount_even_add_two,positiveCount_even_add_two]
    push_cast
    ring
  rw [shell_eq_tuple m _ true,shell_eq_tuple m _ true]
  convert pair_push_pattern_le_free_add hB hb _ _ eP eN hc (tupleSphere m _) (tupleSphere m _) using 1
  all_goals push_cast
  all_goals rfl

end RankTwo

theorem coefficientPair_nonneg {G : Type uG} (h k : G →₀ ℝ)
    (hh : ∀ g, 0 ≤ h g) (hk : ∀ g, 0 ≤ k g) : 0 ≤ coefficientPair h k := by
  exact Finset.sum_nonneg (fun g _ => mul_nonneg (hh g) (hk g))

theorem coefficientPair_eq_zero_of_disjoint {G : Type uG} (h k : G →₀ ℝ)
    (hd : Disjoint h.support k.support) : coefficientPair h k = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro g hg
  have hk : k g = 0 := by
    by_contra hn
    exact Finset.disjoint_left.mp hd hg (Finsupp.mem_support_iff.mpr hn)
  simp [hk]

theorem pushCoefficients_nonneg {G : Type uG} {H : Type uH} [Group G] [Group H]
    (f : G →* H) (h : G →₀ ℝ) (hh : ∀ g, 0 ≤ h g) (a : H) :
    0 ≤ pushCoefficients f h a := by
  classical
  change 0 ≤ Finsupp.mapDomain f h a
  rw [Finsupp.mapDomain,Finsupp.sum_apply]
  apply Finset.sum_nonneg
  intro g _
  change 0 ≤ Finsupp.single (f g) (h g) a
  rw [Finsupp.single_apply]
  split_ifs
  · exact hh g
  · rfl

namespace RankTwo

def shellWeight (m k : ℕ) : ℝ := 1 / ((m : ℝ)*((m : ℝ)-1)^k)

theorem shellWeight_nonneg {m : ℕ} (hm : 2 ≤ m) (k : ℕ) : 0 ≤ shellWeight m k := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : 0 ≤ (m : ℝ)-1 := by linarith
  unfold shellWeight
  positivity

theorem shellWeight_product_bound {m : ℕ} (hm : 2 ≤ m) (k l : ℕ) :
    shellWeight m k * shellWeight m l * (m : ℝ)^(k+l+1) ≤ 2^(k+l)/(m : ℝ) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (0 : ℝ) < m := by linarith
  have hq : (0 : ℝ) < (m : ℝ)-1 := by linarith
  have he : shellWeight m k * shellWeight m l * (m : ℝ)^(k+l+1) =
      ((m : ℝ)/((m : ℝ)-1))^(k+l)/(m : ℝ) := by
    simp only [shellWeight,pow_succ,pow_add,div_pow]
    field_simp
  rw [he]
  apply div_le_div_of_nonneg_right _ hp.le
  apply pow_le_pow_left₀ (by positivity)
  apply (div_le_iff₀ hq).mpr
  linarith

def rightConstant (k : ℕ) : ℝ := 2^(2*k)*(2*k+1 : ℝ)^(2*k+1)
def leftConstant (k l : ℕ) : ℝ := 2^(k+l)*(k+l+2 : ℝ)^2*(k+l+2 : ℝ)^(k+l+2)

theorem pair_rightShell_le {m k B : ℕ} (hm : 2 ≤ m)
    (hB : m*((2*k+1)+(2*k+1)) < B) (hb : 2 ≤ B) :
    coefficientSqNorm (pushCoefficients (prefixHom B m) (Radial.rightShell m k)) ≤
      rightConstant k / m := by
  rw [Radial.rightShell,map_smul,coefficientSqNorm_smul,← coefficientPair_self]
  change (shellWeight m k)^2 * _ ≤ _
  calc
    _ ≤ (shellWeight m k)^2 * ((m : ℝ)^(2*k+1)*(2*k+1 : ℝ)^(2*k+1)) :=
      mul_le_mul_of_nonneg_left (pair_shell_right_le hB hb) (sq_nonneg _)
    _ = (2*k+1 : ℝ)^(2*k+1) *
        (shellWeight m k * shellWeight m k * (m : ℝ)^(k+k+1)) := by
      rw [show k+k=2*k by omega]; ring
    _ ≤ (2*k+1 : ℝ)^(2*k+1) * (2^(k+k)/(m : ℝ)) :=
      mul_le_mul_of_nonneg_left (shellWeight_product_bound hm k k) (by positivity)
    _ = _ := by rw [show k+k=2*k by omega]; unfold rightConstant; ring

theorem pair_leftShell_le_free_add {m k l B : ℕ} (hm : 2 ≤ m)
    (hB : m*((2*k+2)+(2*l+2)) < B) (hb : 2 ≤ B) :
    coefficientPair (pushCoefficients (prefixHom B m) (Radial.leftShell m k))
      (pushCoefficients (prefixHom B m) (Radial.leftShell m l)) ≤
      coefficientPair (Radial.leftShell m k) (Radial.leftShell m l) + leftConstant k l / m := by
  simp only [Radial.leftShell,map_smul,coefficientPair_smul_left,coefficientPair_smul_right]
  change shellWeight m l * (shellWeight m k * _) ≤
    shellWeight m l * (shellWeight m k * _) + _
  have hh := mul_le_mul_of_nonneg_left (pair_shell_left_le_free_add hB hb)
    (mul_nonneg (shellWeight_nonneg hm k) (shellWeight_nonneg hm l))
  have he := mul_le_mul_of_nonneg_left (shellWeight_product_bound hm k l)
    (show 0 ≤ (k+l+2 : ℝ)^2*(k+l+2 : ℝ)^(k+l+2) by positivity)
  calc
    _ = (shellWeight m k * shellWeight m l) * _ := by ring
    _ ≤ (shellWeight m k * shellWeight m l) *
        (coefficientPair (Radial.shell true (2*k+2)) (Radial.shell true (2*l+2)) +
          ((k+l+2 : ℝ)^2*(k+l+2 : ℝ)^(k+l+2))*(m : ℝ)^(k+l+1)) := hh
    _ = shellWeight m l * (shellWeight m k *
        coefficientPair (Radial.shell true (2*k+2)) (Radial.shell true (2*l+2))) +
        ((k+l+2 : ℝ)^2*(k+l+2 : ℝ)^(k+l+2)) *
          (shellWeight m k * shellWeight m l * (m : ℝ)^(k+l+1)) := by ring
    _ ≤ shellWeight m l * (shellWeight m k *
        coefficientPair (Radial.shell true (2*k+2)) (Radial.shell true (2*l+2))) +
        ((k+l+2 : ℝ)^2*(k+l+2 : ℝ)^(k+l+2)) * (2^(k+l)/(m : ℝ)) := add_le_add le_rfl he
    _ = _ := by unfold leftConstant; ring

theorem pair_leftShell_free_le {m : ℕ} (hm : 2 ≤ m) (k l : ℕ) :
    coefficientPair (Radial.leftShell m k) (Radial.leftShell m l) ≤ if k=l then 1 else 0 := by
  classical
  by_cases h : k=l
  · subst l
    rw [ite_eq_left rfl,coefficientPair_self,Radial.sqNorm_leftShell m k hm]
    have hp : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    apply (div_le_iff₀ hp).mpr
    linarith
  · rw [ite_eq_right h,coefficientPair_eq_zero_of_disjoint _ _ (Radial.leftShell_disjoint m h)]

theorem leftShell_nonneg {m : ℕ} (hm : 2 ≤ m) (k : ℕ) (g : FreeGroup (Fin m)) :
    0 ≤ Radial.leftShell m k g := by
  change 0 ≤ shellWeight m k * Radial.shell true (2*k+2) g
  apply mul_nonneg (shellWeight_nonneg hm k)
  rw [Radial.shell_apply]
  split_ifs <;> norm_num

theorem pair_leftShell_push_nonneg {m B : ℕ} (hm : 2 ≤ m) (k l : ℕ) :
    0 ≤ coefficientPair (pushCoefficients (prefixHom B m) (Radial.leftShell m k))
      (pushCoefficients (prefixHom B m) (Radial.leftShell m l)) := by
  apply coefficientPair_nonneg
  · exact pushCoefficients_nonneg _ _ (leftShell_nonneg hm k)
  · exact pushCoefficients_nonneg _ _ (leftShell_nonneg hm l)

def partialConstant (N : ℕ) : ℝ := (N : ℝ)*∑ k ∈ Finset.range N, rightConstant k
def inverseConstant (N : ℕ) : ℝ :=
  (1/(N+1 : ℝ))^2*(N+1 : ℝ)*∑ k ∈ Finset.range (N+1), partialConstant (k+1)
def residualConstant (N : ℕ) : ℝ :=
  (1/(N+1 : ℝ))^2*∑ k ∈ Finset.range (N+1), ∑ l ∈ Finset.range (N+1), leftConstant k l

theorem neg_one_pow_sq (k : ℕ) : ((-1 : ℝ)^k)^2 = 1 := by
  rw [← pow_mul,Nat.mul_comm,pow_mul]
  norm_num

theorem sqNorm_push_partial_le {m N B : ℕ} (hm : 2 ≤ m)
    (hB : m*(4*N+4) < B) (hb : 2 ≤ B) (j : ℕ) (hj : j ≤ N+1) :
    coefficientSqNorm (pushCoefficients (prefixHom B m) (Radial.partialInverse m j)) ≤
      partialConstant j / m := by
  rw [Radial.partialInverse,map_sum]
  calc
    _ ≤ ((Finset.range j).card : ℝ)*∑ k ∈ Finset.range j,
        coefficientSqNorm (pushCoefficients (prefixHom B m) ((-1 : ℝ)^k • Radial.rightShell m k)) :=
      coefficientSqNorm_sum_le _ _
    _ ≤ (j : ℝ)*∑ k ∈ Finset.range j, rightConstant k / m := by
      rw [Finset.card_range]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro k hk
      rw [map_smul,coefficientSqNorm_smul,neg_one_pow_sq,one_mul]
      apply pair_rightShell_le hm _ hb
      have hkN : k ≤ N := by have := Finset.mem_range.mp hk; omega
      exact lt_of_le_of_lt (Nat.mul_le_mul_left m (by omega)) hB
    _ = _ := by rw [← Finset.sum_div]; unfold partialConstant; ring

theorem sqNorm_push_inverse_le {m N B : ℕ} (hm : 2 ≤ m)
    (hB : m*(4*N+4) < B) (hb : 2 ≤ B) :
    coefficientSqNorm (pushCoefficients (prefixHom B m) (Radial.averagedInverse m N)) ≤
      inverseConstant N / m := by
  rw [Radial.averagedInverse,map_smul,coefficientSqNorm_smul,map_sum]
  calc
    _ ≤ (1/(N+1 : ℝ))^2 * (((Finset.range (N+1)).card : ℝ)*∑ k ∈ Finset.range (N+1),
        coefficientSqNorm (pushCoefficients (prefixHom B m) (Radial.partialInverse m (k+1)))) :=
      mul_le_mul_of_nonneg_left (coefficientSqNorm_sum_le _ _) (sq_nonneg _)
    _ ≤ (1/(N+1 : ℝ))^2 * ((N+1 : ℝ)*∑ k ∈ Finset.range (N+1), partialConstant (k+1)/m) := by
      simp only [Finset.card_range,Nat.cast_add,Nat.cast_one]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun k hk => sqNorm_push_partial_le hm hB hb (k+1)
        (by have := Finset.mem_range.mp hk; omega))
    _ = _ := by rw [← Finset.sum_div]; unfold inverseConstant; ring

theorem signed_left_pair_le {m B k l : ℕ} (hm : 2 ≤ m)
    (hB : m*((2*k+2)+(2*l+2)) < B) (hb : 2 ≤ B) :
    (-1 : ℝ)^k * ((-1 : ℝ)^l *
      coefficientPair (pushCoefficients (prefixHom B m) (Radial.leftShell m k))
        (pushCoefficients (prefixHom B m) (Radial.leftShell m l))) ≤
      (if k=l then (1 : ℝ) else 0) + leftConstant k l/m := by
  have hsign : (-1 : ℝ)^k*(-1 : ℝ)^l ≤ 1 := by
    rw [← pow_add]
    rcases neg_one_pow_eq_or ℝ (k+l) with h | h <;> simp [h]
  have hp := pair_leftShell_push_nonneg (B := B) hm k l
  have hsign' := mul_le_mul_of_nonneg_right hsign hp
  rw [mul_assoc,one_mul] at hsign'
  exact hsign'.trans ((pair_leftShell_le_free_add hm hB hb).trans
    (add_le_add (pair_leftShell_free_le hm k l) le_rfl))

theorem sqNorm_signed_left_sum_le {m N B : ℕ} (hm : 2 ≤ m)
    (hB : m*(4*N+4) < B) (hb : 2 ≤ B) :
    coefficientSqNorm (∑ k ∈ Finset.range (N+1), (-1 : ℝ)^k •
      pushCoefficients (prefixHom B m) (Radial.leftShell m k)) ≤
      (N+1 : ℝ) + (∑ k ∈ Finset.range (N+1), ∑ l ∈ Finset.range (N+1), leftConstant k l)/m := by
  classical
  rw [← coefficientPair_self,coefficientPair_sum_left]
  simp_rw [coefficientPair_sum_right,coefficientPair_smul_left,coefficientPair_smul_right]
  calc
    _ ≤ ∑ k ∈ Finset.range (N+1), ∑ l ∈ Finset.range (N+1),
        ((if k=l then (1 : ℝ) else 0) + leftConstant k l / m) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      apply signed_left_pair_le hm (B := B) (k := k) (l := l) _ hb
      have hkN : k ≤ N := by have := Finset.mem_range.mp hk; omega
      have hlN : l ≤ N := by have := Finset.mem_range.mp hl; omega
      exact lt_of_le_of_lt (Nat.mul_le_mul_left m (by omega)) hB
    _ = _ := by
      simp only [Finset.sum_add_distrib,← Finset.sum_div]
      have hdiag : (∑ k ∈ Finset.range (N+1), ∑ l ∈ Finset.range (N+1),
          if k=l then (1 : ℝ) else 0) = N+1 := by
        calc
          _ = ∑ _k ∈ Finset.range (N+1), (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro k hk
            simp [hk]
          _ = _ := by simp
      rw [hdiag]

theorem sqNorm_push_residual_le {m N B : ℕ} (hm : 2 ≤ m)
    (hB : m*(4*N+4) < B) (hb : 2 ≤ B) :
    coefficientSqNorm (pushCoefficients (prefixHom B m)
      (Radial.sumShift (Radial.averagedInverse m N) - Finsupp.single 1 1)) ≤
      1/(N+1 : ℝ)+residualConstant N/m := by
  rw [Radial.sumShift_averagedInverse m N hm,map_smul,coefficientSqNorm_smul,map_sum]
  simp_rw [map_smul]
  calc
    _ ≤ (1/(N+1 : ℝ))^2 * ((N+1 : ℝ) +
        (∑ k ∈ Finset.range (N+1), ∑ l ∈ Finset.range (N+1), leftConstant k l)/m) :=
      mul_le_mul_of_nonneg_left (sqNorm_signed_left_sum_le hm hB hb) (sq_nonneg _)
    _ = _ := by
      unfold residualConstant
      have hN : (N+1 : ℝ) ≠ 0 := by positivity
      field_simp

theorem exists_small_pushed_inverse (ε : ℝ) (hε : 0 < ε) :
    ∃ m B : ℕ, 2 ≤ m ∧ 2 ≤ B ∧ ∃ h : FreeGroup (Fin m) →₀ ℝ,
      coefficientSqNorm (pushCoefficients (prefixHom B m) h) < ε ∧
      coefficientSqNorm (pushCoefficients (prefixHom B m)
        (Radial.sumShift h-Finsupp.single 1 1)) < ε := by
  obtain ⟨N,hN⟩ := exists_nat_one_div_lt (by positivity : 0 < ε/2)
  obtain ⟨m,hm⟩ := exists_nat_gt (max (2 : ℝ) (max (2*inverseConstant N/ε) (2*residualConstant N/ε)))
  have hm2 : 2 ≤ m := by exact_mod_cast ((le_max_left _ _).trans_lt hm).le
  have hmp : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmI : inverseConstant N/m < ε/2 := by
    apply (div_lt_iff₀ hmp).mpr
    have hh := (le_max_left (2*inverseConstant N/ε) _).trans_lt ((le_max_right _ _).trans_lt hm)
    have hh' := (div_lt_iff₀ hε).mp hh
    nlinarith
  have hmR : residualConstant N/m < ε/2 := by
    apply (div_lt_iff₀ hmp).mpr
    have hh := (le_max_right _ (2*residualConstant N/ε)).trans_lt ((le_max_right _ _).trans_lt hm)
    have hh' := (div_lt_iff₀ hε).mp hh
    nlinarith
  let B := m*(4*N+4)+2
  have hB : m*(4*N+4)<B := by dsimp [B]; omega
  have hb : 2 ≤ B := by dsimp [B]; omega
  refine ⟨m,B,hm2,hb,Radial.averagedInverse m N,?_,?_⟩
  · exact (sqNorm_push_inverse_le hm2 hB hb).trans_lt (hmI.trans (by linarith))
  · exact (sqNorm_push_residual_le hm2 hB hb).trans_lt (by linarith)

def twoGenerator (b : Bool) : FreeGroup (Fin 2) := FreeGroup.of (if b then 0 else 1)

def realizeSummand (b : Bool) : Multiplicative ℤ →* FreeGroup (Fin 2) where
  toFun z := twoGenerator b ^ Multiplicative.toAdd z
  map_one' := zpow_zero _
  map_mul' z w := zpow_add _ (Multiplicative.toAdd z) (Multiplicative.toAdd w)

def realize : SyllableGroup →* FreeGroup (Fin 2) := Monoid.CoprodI.lift realizeSummand

@[simp] theorem realize_syllable (b : Bool) (z : ℤ) : realize (syllable b z) = twoGenerator b ^ z := by
  simp [realize,syllable,realizeSummand]

def syllabify : FreeGroup (Fin 2) →* SyllableGroup :=
  FreeGroup.lift (fun i => if i = 0 then syllable true 1 else syllable false 1)

@[simp] theorem syllabify_generator (b : Bool) : syllabify (twoGenerator b) = syllable b 1 := by
  cases b <;> simp [syllabify,twoGenerator]

@[simp] theorem syllable_zpow (b : Bool) (z : ℤ) : (syllable b 1)^z = syllable b z := by
  unfold syllable
  rw [← map_zpow]
  congr 1
  change Multiplicative.ofAdd (z • (1 : ℤ)) = Multiplicative.ofAdd z
  simp

theorem syllabify_realize : syllabify.comp realize = MonoidHom.id _ := by
  apply Monoid.CoprodI.ext_hom
  intro b
  apply DFunLike.ext
  intro z
  change syllabify (realize (syllable b (Multiplicative.toAdd z))) = syllable b (Multiplicative.toAdd z)
  rw [realize_syllable,map_zpow,syllabify_generator,syllable_zpow]

theorem realize_injective : Function.Injective realize := by
  intro x y he
  have hh := congrArg syllabify he
  simpa only [← MonoidHom.comp_apply,syllabify_realize,MonoidHom.id_apply] using hh

end RankTwo

theorem pushCoefficients_comp {G : Type uG} {H : Type uH} {K : Type uK} [Group G] [Group H] [Group K]
    (f : G →* H) (g : H →* K) (h : G →₀ ℝ) :
    pushCoefficients (g.comp f) h = pushCoefficients g (pushCoefficients f h) := by
  induction h using Finsupp.induction_linear with
  | zero => simp
  | add h k ih ik => simp only [map_add,ih,ik]
  | single a c => simp

theorem coefficientSqNorm_shift {G : Type uG} [Group G] (g : G) (h : Coeff G) :
    coefficientSqNorm (coefficientShift g h) = coefficientSqNorm h := by
  rw [coefficientShift,Finsupp.domCongr_apply,Finsupp.equivMapDomain_eq_mapDomain]
  exact Finsupp.sum_mapDomain_index_inj (Equiv.mulLeft g).injective

theorem freeCocycle_zpow_of_zero {ι : Type uι} (h : ι → Coeff (FreeGroup ι))
    (g : FreeGroup ι) (hg : freeCocycle h g = 0) (k : ℤ) : freeCocycle h (g^k) = 0 := by
  cases k with
  | ofNat k => simpa using freeCocycle_pow_of_zero h g hg k
  | negSucc k => simp only [zpow_negSucc,freeCocycle_inv,freeCocycle_pow_of_zero h g hg,map_zero,neg_zero]

namespace RankTwo

def concretePrefix (B j : ℕ) : FreeGroup (Fin 2) := realize (segment (runExponent B) 0 j)
def concreteWord (B m : ℕ) : FreeGroup (Fin 2) := concretePrefix B (m+1) * twoGenerator true

def concretePrefixHom (B m : ℕ) : FreeGroup (Fin m) →* FreeGroup (Fin 2) :=
  realize.comp (prefixHom B m)

@[simp] theorem concretePrefixHom_of (B m : ℕ) (i : Fin m) :
    concretePrefixHom B m (FreeGroup.of i) = concretePrefix B (i.val+2) := by
  simp [concretePrefixHom,prefixHom,concretePrefix]

@[simp] theorem concretePrefix_zero (B : ℕ) : concretePrefix B 0 = 1 := by simp [concretePrefix]
@[simp] theorem concretePrefix_succ (B j : ℕ) :
    concretePrefix B (j+1) = concretePrefix B j *
      (twoGenerator true * (twoGenerator false)^(runExponent B j)) := by
  simp only [concretePrefix,segment_succ,Nat.zero_add,map_mul,piece,realize_syllable,zpow_one]

theorem cocycle_twoGenerator_true (h : Coeff (FreeGroup (Fin 2))) :
    freeCocycle (firstCoefficients h) (twoGenerator true) = h := by
  simp [twoGenerator,firstCoefficients]

theorem cocycle_twoGenerator_false (h : Coeff (FreeGroup (Fin 2))) :
    freeCocycle (firstCoefficients h) (twoGenerator false) = 0 := by
  simp [twoGenerator,firstCoefficients]

theorem cocycle_concretePrefix (B m : ℕ) (h : Coeff (FreeGroup (Fin 2))) :
    freeCocycle (firstCoefficients h) (concretePrefix B m) =
      ∑ j ∈ Finset.range m, coefficientShift (concretePrefix B j) h := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [concretePrefix_succ,freeCocycle_mul,freeCocycle_mul,
      cocycle_twoGenerator_true,freeCocycle_zpow_of_zero _ _ (cocycle_twoGenerator_false h)]
    simp only [map_zero,add_zero,ih,Finset.sum_range_succ]

theorem cocycle_concreteWord (B m : ℕ) (h : Coeff (FreeGroup (Fin 2))) :
    freeCocycle (firstCoefficients h) (concreteWord B m) =
      h + coefficientShift (concretePrefix B 1) h +
        ∑ i : Fin m, coefficientShift (concretePrefix B (i.val+2)) h := by
  rw [concreteWord,freeCocycle_mul,cocycle_concretePrefix,cocycle_twoGenerator_true,
    ← Finset.sum_range_succ]
  rw [Finset.sum_range_succ',Finset.sum_range_succ']
  simp only [concretePrefix_zero,coefficientShift_one,Nat.zero_add]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => coefficientShift (concretePrefix B (k+2)) h)]
  simpa only [Nat.add_assoc,Nat.one_add] using (by abel :
    (∑ j ∈ Finset.range m, coefficientShift (concretePrefix B (j+1+1)) h) +
        coefficientShift (concretePrefix B 1) h + h =
      h + coefficientShift (concretePrefix B 1) h +
        (∑ j ∈ Finset.range m, coefficientShift (concretePrefix B (j+2)) h))

theorem push_sumShift (B m : ℕ) (h : FreeGroup (Fin m) →₀ ℝ) :
    pushCoefficients (concretePrefixHom B m) (Radial.sumShift h) =
      ∑ i : Fin m, coefficientShift (concretePrefix B (i.val+2))
        (pushCoefficients (concretePrefixHom B m) h) := by
  rw [Radial.sumShift_apply,map_sum]
  simp only [pushCoefficients_shift,concretePrefixHom_of]

theorem rank_two_cocycle_identity (B m : ℕ) (h : FreeGroup (Fin m) →₀ ℝ) :
    freeCocycle (firstCoefficients (pushCoefficients (concretePrefixHom B m) h)) (concreteWord B m) =
      pushCoefficients (concretePrefixHom B m) h +
        coefficientShift (concretePrefix B 1) (pushCoefficients (concretePrefixHom B m) h) +
        pushCoefficients (concretePrefixHom B m) (Radial.sumShift h) := by
  rw [cocycle_concreteWord,push_sumShift]

theorem sqNorm_concrete_push (B m : ℕ) (h : FreeGroup (Fin m) →₀ ℝ) :
    coefficientSqNorm (pushCoefficients (concretePrefixHom B m) h) =
      coefficientSqNorm (pushCoefficients (prefixHom B m) h) := by
  rw [concretePrefixHom,pushCoefficients_comp,sqNorm_pushCoefficients realize realize_injective]

end RankTwo

theorem smallCocycleTwo (η : ℝ) (hη : 0 < η) :
    ∃ (w : FreeGroup (Fin 2)) (h : Coeff (FreeGroup (Fin 2))),
      coefficientNorm h < η ∧
        coefficientNorm (freeCocycle (firstCoefficients h) w-Finsupp.single 1 1) < η := by
  obtain ⟨m,B,_hm,_hB,h,hh,hr⟩ := RankTwo.exists_small_pushed_inverse (η^2/16) (by positivity)
  let f := RankTwo.concretePrefixHom B m
  let h₂ := pushCoefficients f h
  have hsmall : coefficientSqNorm h₂ < η^2/16 := by
    simpa only [h₂,f,RankTwo.sqNorm_concrete_push] using hh
  have hrsmall : coefficientSqNorm (pushCoefficients f (Radial.sumShift h-Finsupp.single 1 1)) < η^2/16 := by
    simpa only [f,RankTwo.sqNorm_concrete_push] using hr
  refine ⟨RankTwo.concreteWord B m,h₂,?_,?_⟩
  · apply (Real.sqrt_lt' hη).mpr
    exact hsmall.trans (by nlinarith [sq_pos_of_pos hη])
  · apply (Real.sqrt_lt' hη).mpr
    change coefficientSqNorm (freeCocycle (firstCoefficients h₂) (RankTwo.concreteWord B m)-_) < η^2
    have hid : freeCocycle (firstCoefficients h₂) (RankTwo.concreteWord B m)-Finsupp.single 1 1 =
        (h₂+coefficientShift (RankTwo.concretePrefix B 1) h₂) +
          pushCoefficients f (Radial.sumShift h-Finsupp.single 1 1) := by
      dsimp only [h₂,f]
      rw [RankTwo.rank_two_cocycle_identity,map_sub]
      simp only [pushCoefficients_single,map_one]
      abel
    rw [hid]
    have hshift := coefficientSqNorm_shift (RankTwo.concretePrefix B 1) h₂
    have hsum := coefficientSqNorm_add_le h₂ (coefficientShift (RankTwo.concretePrefix B 1) h₂)
    have htot := coefficientSqNorm_add_le (h₂+coefficientShift (RankTwo.concretePrefix B 1) h₂)
      (pushCoefficients f (Radial.sumShift h-Finsupp.single 1 1))
    nlinarith

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

namespace FreeGroupFactorMain

noncomputable section

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

attribute [local instance] Classical.propDecidable

open UnitaryEvaluation
theorem one_step_of_coefficient_estimate (n : ℕ)
    (hc : ∀ η : ℝ, 0 < η → ∃ (w : FreeGroup (Fin n)) (h : Coeff (FreeGroup (Fin n))),
      coefficientNorm h < η ∧
        coefficientNorm (freeCocycle (firstCoefficients h) w-Finsupp.single 1 1) < η) {ε : ℝ} (hε : 0 < ε) :
    ∃ α : groupVonNeumann (FreeGroup (Option (Fin n))) ≃⋆ₐ[ℂ] groupVonNeumann (FreeGroup (Option (Fin n))),
      (∀ T, canonicalTrace (α T) = canonicalTrace T) ∧
      @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option (Fin n))))
        (groupUltraweakTopology (FreeGroup (Option (Fin n)))) α ∧
      ∃ w : FreeGroup (Fin n),
        (∀ j : Fin n, ‖α (groupUnitary (FreeGroup.of (some j))) - groupUnitary (FreeGroup.of (some j))‖ < ε) ∧
        twoNorm (α (groupUnitary (FreeGroup.map Option.some w)) - groupUnitary (FreeGroup.of none)) < ε := by
  obtain ⟨l,hl0,hlS,hln,z,hze⟩ := haar_centered_laurent (G := FreeGroup (Option (Fin n)))
    (generatorUnitary (none : Option (Fin n))) (generator_haar (none : Option (Fin n))) (half_pos hε)
  rw [← laurentValue_eq_value] at hlS hln hze
  obtain ⟨w,h,hh,hw⟩ := hc ((ε/2)/(3*(2*(Real.pi+1)))) (by positivity)
  exact one_step_from_laurent n hε l hl0 hlS hln z hze w h hh hw

theorem one_step_two {ε : ℝ} (hε : 0 < ε) :
    ∃ α : groupVonNeumann (FreeGroup (Option (Fin 2))) ≃⋆ₐ[ℂ] groupVonNeumann (FreeGroup (Option (Fin 2))),
      (∀ T, canonicalTrace (α T) = canonicalTrace T) ∧
      @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option (Fin 2))))
        (groupUltraweakTopology (FreeGroup (Option (Fin 2)))) α ∧
      ∃ w : FreeGroup (Fin 2),
        (∀ j : Fin 2, ‖α (groupUnitary (FreeGroup.of (some j))) - groupUnitary (FreeGroup.of (some j))‖ < ε) ∧
        twoNorm (α (groupUnitary (FreeGroup.map Option.some w)) - groupUnitary (FreeGroup.of none)) < ε :=
  one_step_of_coefficient_estimate 2 smallCocycleTwo hε

theorem one_step_ge_two (n : ℕ) (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ α : groupVonNeumann (FreeGroup (Option (Fin n))) ≃⋆ₐ[ℂ] groupVonNeumann (FreeGroup (Option (Fin n))),
      (∀ T, canonicalTrace (α T) = canonicalTrace T) ∧
      @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option (Fin n))))
        (groupUltraweakTopology (FreeGroup (Option (Fin n)))) α ∧
      ∃ w : FreeGroup (Fin n),
        (∀ j : Fin n, ‖α (groupUnitary (FreeGroup.of (some j))) - groupUnitary (FreeGroup.of (some j))‖ < ε) ∧
        twoNorm (α (groupUnitary (FreeGroup.map Option.some w)) - groupUnitary (FreeGroup.of none)) < ε := by
  by_cases h : n = 2
  · subst n
    exact one_step_two hε
  · exact one_step n (by omega) hε

namespace Generation

theorem orbit_step_ge_two (n : ℕ) (hn : 2 ≤ n)
    (Φ : Ambient n ≃⋆ₐ[ℂ] Ambient n)
    (ht : ∀ T, canonicalTrace (Φ T) = canonicalTrace T) {θ : ℝ} (hθ : 0 < θ) :
    ∃ V ∈ orbit n, dist V (mapTuple Φ (initial n)) < θ ∧
      ∃ w : FreeGroup (Fin n), ∀ j : Option (Fin n),
        twoNorm ((wordTuple V (fun j => j.elim w FreeGroup.of) j : Ambient n) -
          (mapTuple Φ generatorUnitary j : Ambient n)) < θ := by
  obtain ⟨α,hαt,_hαn,w,hgen,hword⟩ := one_step_ge_two n hn hθ
  let V : Tuple n := mapTuple (α.trans Φ) (initial n)
  have hdist : dist V (mapTuple Φ (initial n)) < θ := by
    apply (dist_pi_lt_iff hθ).mpr
    intro j
    change dist (Φ (α (groupUnitary (FreeGroup.of (some j))))) (Φ (groupUnitary (FreeGroup.of (some j)))) < θ
    have hnorm (T : Ambient n) : ‖Φ T‖ = ‖T‖ :=
      NonUnitalStarAlgHom.norm_map Φ.toStarAlgHom Φ.injective T
    rw [dist_eq_norm, ← map_sub, hnorm]
    exact hgen j
  refine ⟨V,⟨α.trans Φ,?_,rfl⟩,hdist,w,?_⟩
  · intro T
    simp only [StarAlgEquiv.trans_apply,ht,hαt]
  · intro j
    cases j with
    | none =>
      change twoNorm (word V w-Φ (groupUnitary (FreeGroup.of none))) < θ
      rw [show V = mapTuple (α.trans Φ) (initial n) from rfl,word_mapTuple,
        word_initial,StarAlgEquiv.trans_apply,← map_sub,twoNorm_iso Φ ht]
      exact hword
    | some j =>
      change twoNorm ((V j : Ambient n)-Φ (groupUnitary (FreeGroup.of (some j)))) < θ
      have hj := (dist_pi_lt_iff hθ).mp hdist j
      change dist (V j : Ambient n) (Φ (groupUnitary (FreeGroup.of (some j)))) < θ at hj
      rw [dist_eq_norm] at hj
      exact (twoNorm_le_norm _).trans_lt hj

end Generation

open Generation

end

end FreeGroupFactorMain

end OAI
end

theorem solution : type_of% @OAI.FreeGroupFactorMain.Generation.orbit_step_ge_two := @OAI.FreeGroupFactorMain.Generation.orbit_step_ge_two
