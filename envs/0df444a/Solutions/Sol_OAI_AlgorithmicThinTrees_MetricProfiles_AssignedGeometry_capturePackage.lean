-- Prove2me | solution 1 for OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.capturePackage
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:49:56.426919+00:00
-- url     : https://prove2.me/submissions/954b8873-48d0-40ec-a189-1544083eff03

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT001
import Definitions.Def_OAIQ241TT002
import Definitions.Def_OAIQ241TT003

section
-- module Solutions.OAIQ241_TT.ThinTrees_SpectralPacking
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Hermitian.instFiniteDimensionalRealSubtypeMatMemSubmoduleH
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uι uι2 uV uι3 uV2 uV3 uV4 uV5 uV6 uι4 uη

section
open scoped Classical
open Matrix

namespace StrongThinTree.Spectral
noncomputable section
open Finset LinearMap
open scoped InnerProductSpace
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma frobSq_eq_sum {ι : Type uι} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (T : E →ₗ[ℝ] E) :
    frobSq T = ∑i, ‖T (b i)‖ ^ 2 := by
  rw [frobSq, LinearMap.trace_eq_sum_inner _ b]
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

lemma frobSq_nonneg (T : E →ₗ[ℝ] E) : 0 ≤ frobSq T := by
  rw [frobSq_eq_sum (stdOrthonormalBasis ℝ E)]
  positivity

lemma frobSq_adjoint (T : E →ₗ[ℝ] E) : frobSq T.adjoint = frobSq T := by
  rw [frobSq, adjoint_adjoint, LinearMap.trace_comp_comm', frobSq]

omit [FiniteDimensional ℝ E] in
lemma trace_bound (T : E →ₗ[ℝ] E) {ι : Type uι2} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    |LinearMap.trace ℝ E T| ≤ ∑i, ‖T (b i)‖ := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro i hi
  calc
    |⟪b i, T (b i)⟫_ℝ| ≤ ‖b i‖ * ‖T (b i)‖ := abs_real_inner_le_norm _ _
    _ = ‖T (b i)‖ := by rw [b.orthonormal.norm_eq_one, one_mul]

lemma norm_eigenvector (T : E →ₗ[ℝ] E) (i : Fin (Module.finrank ℝ E)) :
    ‖T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i)‖ = T.singularValues i := by
  let h := T.isSymmetric_adjoint_comp_self
  let b := h.eigenvectorBasis rfl
  have he := h.apply_eigenvectorBasis rfl i
  have he' := congrArg (fun x => ⟪b i, x⟫_ℝ) he
  change ⟪b i, T.adjoint (T (b i))⟫_ℝ = ⟪b i, h.eigenvalues rfl i • b i⟫_ℝ at he'
  rw [adjoint_inner_right, real_inner_self_eq_norm_sq, inner_smul_right,
    real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one, one_pow, mul_one] at he'
  rw [T.singularValues_fin rfl i, ← he', Real.sqrt_sq (norm_nonneg _)]

lemma trace_le_singular_sum (T : E →ₗ[ℝ] E) :
    |LinearMap.trace ℝ E T| ≤ ∑i : Fin (Module.finrank ℝ E), T.singularValues i := by
  simpa only [norm_eigenvector] using trace_bound T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl)

lemma frobSq_eq_singular_sum (T : E →ₗ[ℝ] E) :
    frobSq T = ∑i : Fin (Module.finrank ℝ E), T.singularValues i ^ 2 := by
  rw [frobSq_eq_sum (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl)]
  simp only [norm_eigenvector]

lemma projection_symmetric (K : Submodule ℝ E) : K.starProjection.toLinearMap.IsSymmetric := by
  intro u v
  exact K.inner_starProjection_left_eq_right u v

lemma projection_sq (K : Submodule ℝ E) :
    K.starProjection.toLinearMap ∘ₗ K.starProjection.toLinearMap = K.starProjection.toLinearMap := by
  ext v
  exact K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem v)

lemma projection_trace (K : Submodule ℝ E) :
    LinearMap.trace ℝ E K.starProjection.toLinearMap = (Module.finrank ℝ K : ℝ) := by
  exact (show LinearMap.IsProj K K.starProjection.toLinearMap from
    ⟨K.starProjection_apply_mem, fun v hv => K.starProjection_eq_self_iff.mpr hv⟩).trace

lemma projection_inner (K : Submodule ℝ E) (v : E) :
    ⟪v, K.starProjection v⟫_ℝ = ‖K.starProjection v‖ ^ 2 := by
  rw [real_inner_comm]
  exact K.re_inner_starProjection_eq_normSq v

lemma frobSq_projection_le (K : Submodule ℝ E) (T : E →ₗ[ℝ] E) :
    frobSq (K.starProjection.toLinearMap ∘ₗ T) ≤ frobSq T := by
  rw [frobSq_eq_sum (stdOrthonormalBasis ℝ E), frobSq_eq_sum (stdOrthonormalBasis ℝ E)]
  apply sum_le_sum
  intro i hi
  exact pow_le_pow_left₀ (norm_nonneg _) (K.norm_starProjection_apply_le _) 2

lemma frobSq_projection (K : Submodule ℝ E) (T : E →ₗ[ℝ] E) :
    frobSq (K.starProjection.toLinearMap ∘ₗ T) =
      LinearMap.trace ℝ E ((T ∘ₗ T.adjoint) ∘ₗ K.starProjection.toLinearMap) := by
  let P := K.starProjection.toLinearMap
  have hP : P.adjoint = P := (projection_symmetric K).adjoint_eq
  have hPP : P ∘ₗ P = P := projection_sq K
  change LinearMap.trace ℝ E ((P ∘ₗ T).adjoint ∘ₗ (P ∘ₗ T)) = _
  have heq : (P ∘ₗ T).adjoint ∘ₗ (P ∘ₗ T) = T.adjoint ∘ₗ (P ∘ₗ T) := by
    rw [adjoint_comp, hP]
    ext v
    change T.adjoint (P (P (T v))) = T.adjoint (P (T v))
    exact congrArg T.adjoint (congrArg (fun f : E →ₗ[ℝ] E => f (T v)) hPP)
  rw [heq, LinearMap.trace_comp_comm', comp_assoc, LinearMap.trace_comp_comm']

lemma weighted_tail_le {d k : ℕ} (hk : k ≤ d) (s w : Fin d → ℝ)
    (hs : Antitone s) (hn : ∀i, 0 ≤ s i)
    (hw : ∀i, 0 ≤ w i ∧ w i ≤ 1)
    (hsum : (d - k : ℕ) ≤ ∑i, w i) :
    (∑i with k ≤ i.val, s i) ≤ ∑i, s i * w i := by
  classical
  by_cases hkd : k = d
  · subst k
    have hz : univ.filter (fun i : Fin d => d ≤ i.val) = ∅ := by
      apply eq_empty_of_forall_notMem
      intro i hi
      exact (not_le_of_gt i.isLt) (mem_filter.mp hi).2
    rw [hz, sum_empty]
    exact sum_nonneg (fun i _ => mul_nonneg (hn i) (hw i).1)
  have hkd' : k < d := lt_of_le_of_ne hk hkd
  let c := s ⟨k, hkd'⟩
  let L := univ.filter (fun i : Fin d => i.val < k)
  let R := univ.filter (fun i : Fin d => k ≤ i.val)
  have hc : 0 ≤ c := hn _
  have hRcard : R.card = d - k := by
    suffices L.card = k by
      have hcard := card_filter_add_card_filter_not (s := (univ : Finset (Fin d))) (p := fun i => i.val < k)
      simp only [card_univ, Fintype.card_fin, not_lt] at hcard
      change L.card + R.card = d at hcard
      omega
    change (univ.filter (fun i : Fin d => i.val < k)).card = k
    calc
      _ = (univ : Finset (Fin k)).card := by
        apply card_bij (fun i hi => (⟨i.val, (mem_filter.mp hi).2⟩ : Fin k))
        · intro i hi; exact mem_univ _
        · intro i hi j hj he; exact Fin.ext (congrArg (fun x : Fin k => x.val) he)
        · intro j hj
          refine ⟨⟨j.val, j.isLt.trans_le hk⟩, mem_filter.mpr ⟨mem_univ _, j.isLt⟩, ?_⟩
          rfl
      _ = k := by simp
  have hsplit (f : Fin d → ℝ) : (∑i ∈ L, f i) + (∑i ∈ R, f i) = ∑i, f i := by
    simpa only [L, R, not_lt] using (sum_filter_add_sum_filter_not univ (fun i : Fin d => i.val < k) f)
  have hl : c * (∑i ∈ L, w i) ≤ ∑i ∈ L, s i * w i := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_right (hs (by exact (mem_filter.mp hi).2.le)) (hw i).1
  have hr : (∑i ∈ R, s i) - ∑i ∈ R, s i * w i ≤ c * ((d - k : ℕ) - ∑i ∈ R, w i) := by
    have hcard : (R.card : ℝ) = ∑i ∈ R, (1 : ℝ) := by simp
    rw [← hRcard, hcard, ← sum_sub_distrib, ← sum_sub_distrib, mul_sum]
    apply sum_le_sum
    intro i hi
    have hsic : s i ≤ c := hs (by exact (mem_filter.mp hi).2)
    have h := mul_le_mul_of_nonneg_right hsic (sub_nonneg.mpr (hw i).2)
    nlinarith
  have hwc : c * ((d - k : ℕ) - ∑i ∈ R, w i) ≤ c * ∑i ∈ L, w i := by
    apply mul_le_mul_of_nonneg_left _ hc
    have hspl := hsplit w
    linarith
  have hspl := hsplit (fun i => s i * w i)
  change (∑i ∈ R, s i) ≤ _
  linarith

lemma eigenvalue_eq_singular_sq (T : E →ₗ[ℝ] E) (i : Fin (Module.finrank ℝ E)) :
    T.isSymmetric_adjoint_comp_self.eigenvalues rfl i = T.singularValues i ^ 2 := by
  let h := T.isSymmetric_adjoint_comp_self
  let b := h.eigenvectorBasis rfl
  have he' := congrArg (fun x => ⟪b i, x⟫_ℝ) (h.apply_eigenvectorBasis rfl i)
  change ⟪b i, T.adjoint (T (b i))⟫_ℝ = ⟪b i, h.eigenvalues rfl i • b i⟫_ℝ at he'
  rw [adjoint_inner_right, real_inner_self_eq_norm_sq, inner_smul_right,
    real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one, one_pow, mul_one] at he'
  rw [← he']
  exact congrArg (fun x : ℝ => x ^ 2) (norm_eigenvector T i)

lemma trace_adjoint (T : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E T.adjoint = LinearMap.trace ℝ E T := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ E),
    LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ E)]
  apply sum_congr rfl
  intro i hi
  rw [adjoint_inner_right, real_inner_comm]

lemma frobSq_projection_eigenbasis (K : Submodule ℝ E) (T : E →ₗ[ℝ] E) :
    frobSq (K.starProjection.toLinearMap ∘ₗ T) =
      ∑i : Fin (Module.finrank ℝ E), T.adjoint.singularValues i ^ 2 *
        ⟪T.adjoint.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i,
          K.starProjection (T.adjoint.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i)⟫_ℝ := by
  let h := T.adjoint.isSymmetric_adjoint_comp_self
  let b := h.eigenvectorBasis rfl
  rw [frobSq_projection, LinearMap.trace_eq_sum_inner _ b]
  apply sum_congr rfl
  intro i hi
  have he : (T ∘ₗ T.adjoint) (b i) = h.eigenvalues rfl i • b i := by
    calc
      _ = (T.adjoint.adjoint ∘ₗ T.adjoint) (b i) := by rw [adjoint_adjoint]
      _ = _ := h.apply_eigenvectorBasis rfl i
  change ⟪b i, (T ∘ₗ T.adjoint) (K.starProjection (b i))⟫_ℝ = _
  rw [← T.isSymmetric_self_comp_adjoint, he, real_inner_smul_left,
    eigenvalue_eq_singular_sq]

lemma rank_approximation (T C : E →ₗ[ℝ] E) {k : ℕ}
    (hk : k ≤ Module.finrank ℝ E) (hC : Module.finrank ℝ (LinearMap.range C) ≤ k) :
    (∑i : Fin (Module.finrank ℝ E) with k ≤ i.val, T.adjoint.singularValues i ^ 2) ≤
      frobSq (T - C) := by
  let K := (LinearMap.range C)ᗮ
  let P := K.starProjection.toLinearMap
  let b := T.adjoint.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
  let w := fun i => ⟪b i, K.starProjection (b i)⟫_ℝ
  have hw (i : Fin (Module.finrank ℝ E)) : 0 ≤ w i ∧ w i ≤ 1 := by
    change 0 ≤ ⟪b i, K.starProjection (b i)⟫_ℝ ∧ _
    rw [projection_inner]
    constructor
    · positivity
    · have hh := K.norm_starProjection_apply_le (b i)
      rw [b.orthonormal.norm_eq_one] at hh
      dsimp [w]
      rw [projection_inner]
      exact (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans_eq (one_pow _)
  have hsum : ((Module.finrank ℝ E - k : ℕ) : ℝ) ≤ ∑i, w i := by
    have hh := (LinearMap.range C).finrank_add_finrank_orthogonal
    have hd : Module.finrank ℝ E - k ≤ Module.finrank ℝ K := by dsimp [K]; omega
    calc
      _ ≤ (Module.finrank ℝ K : ℝ) := by exact_mod_cast hd
      _ = ∑i, w i := by rw [← projection_trace, LinearMap.trace_eq_sum_inner _ b]; rfl
  have hs : Antitone (fun i : Fin (Module.finrank ℝ E) => T.adjoint.singularValues i ^ 2) := by
    intro i j hij
    exact pow_le_pow_left₀ (T.adjoint.singularValues_nonneg _) (T.adjoint.singularValues_antitone hij) 2
  have hb := weighted_tail_le hk (fun i => T.adjoint.singularValues i ^ 2) w hs
    (fun _ => sq_nonneg _) hw hsum
  have hPC : P ∘ₗ C = 0 := by
    ext x
    change K.starProjection (C x) = 0
    apply K.starProjection_apply_eq_zero_iff.mpr
    change C x ∈ (LinearMap.range C)ᗮᗮ
    rw [Submodule.orthogonal_orthogonal]
    exact LinearMap.mem_range_self C x
  have heq : P ∘ₗ (T - C) = P ∘ₗ T := by rw [comp_sub, hPC, sub_zero]
  calc
    _ ≤ ∑i : Fin (Module.finrank ℝ E), T.adjoint.singularValues i ^ 2 * w i := hb
    _ = frobSq (P ∘ₗ T) := (frobSq_projection_eigenbasis K T).symm
    _ = frobSq (P ∘ₗ (T - C)) := congrArg frobSq heq.symm
    _ ≤ frobSq (T - C) := frobSq_projection_le K (T - C)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in

lemma separated_net {V : Type uV} [DecidableEq V] (F : Finset V) (hF : F.Nonempty)
    (Y : V → E) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ S : Finset V, S ⊆ F ∧ S.Nonempty ∧
      (∀u ∈ S, ∀v ∈ S, u ≠ v → δ < ‖Y u - Y v‖) ∧
      ∀u ∈ F, ∃v ∈ S, ‖Y u - Y v‖ ≤ δ := by
  classical
  let sep : Finset V → Prop := fun S => ∀u ∈ S, ∀v ∈ S, u ≠ v → δ < ‖Y u - Y v‖
  let : DecidablePred sep := fun _ => Classical.propDecidable _
  let good := F.powerset.filter sep
  have hgood : good.Nonempty := ⟨∅, mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _), by simp [sep]⟩⟩
  obtain ⟨S, hS, hmax⟩ := exists_max_image good card hgood
  obtain ⟨hSF, hsep⟩ := mem_filter.mp hS
  have hcover : ∀u ∈ F, ∃v ∈ S, ‖Y u - Y v‖ ≤ δ := by
    intro u hu
    by_contra! hn
    have huS : u ∉ S := by
      intro huS
      have h := hn u huS
      simp only [sub_self, norm_zero] at h
      linarith
    have hnew : insert u S ∈ good := by
      apply mem_filter.mpr
      refine ⟨mem_powerset.mpr (insert_subset hu (mem_powerset.mp hSF)), ?_⟩
      intro x hx y hy hxy
      rcases mem_insert.mp hx with hxU | hxS
      · subst x
        rcases mem_insert.mp hy with hyU | hyS
        · exact (hxy hyU.symm).elim
        · exact hn y hyS
      · rcases mem_insert.mp hy with hyU | hyS
        · subst y
          rw [norm_sub_rev]; exact hn x hxS
        · exact hsep x hxS y hyS hxy
    have hh := hmax _ hnew
    rw [card_insert_of_notMem huS] at hh
    omega
  refine ⟨S, mem_powerset.mp hSF, ?_, hsep, hcover⟩
  obtain ⟨u, hu⟩ := hF
  obtain ⟨v, hv, _⟩ := hcover u hu
  exact ⟨v, hv⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma norm_sub_sq_le_twice (x y : E) : ‖x-y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have hn := norm_sub_le x y
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  have hh : ‖x-y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

omit [FiniteDimensional ℝ E] in
lemma range_le_of_basis {ι : Type uι3} [Fintype ι] (b : Module.Basis ι ℝ E)
    (T : E →ₗ[ℝ] E) (K : Submodule ℝ E) (h : ∀i, T (b i) ∈ K) :
    LinearMap.range T ≤ K := by
  rintro _ ⟨x, rfl⟩
  rw [← b.sum_repr x, map_sum]
  apply K.sum_mem
  intro i hi
  rw [map_smul]
  exact K.smul_mem _ (h i)

omit [FiniteDimensional ℝ E] in

lemma difference_span_rank {V : Type uV2} [DecidableEq V] (S : Finset V)
    (Y : V → E) {v₀ : V} (hv₀ : v₀ ∈ S) :
    Module.finrank ℝ (Submodule.span ℝ
      ((fun v => Y v - Y v₀) '' (S : Set V))) ≤ S.card - 1 := by
  classical
  let A := (S.erase v₀).image (fun v => Y v - Y v₀)
  have heq : Submodule.span ℝ ((fun v => Y v - Y v₀) '' (S : Set V)) =
      Submodule.span ℝ (A : Set E) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨v, hv, rfl⟩
      by_cases heq : v = v₀
      · simp [heq]
      · exact Submodule.subset_span (mem_image.mpr ⟨v, mem_erase.mpr ⟨heq, hv⟩, rfl⟩)
    · apply Submodule.span_mono
      intro x hx
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
      exact ⟨v, mem_of_mem_erase hv, rfl⟩
  rw [heq]
  exact (finrank_span_finset_le_card A).trans ((card_image_le).trans_eq (card_erase_of_mem hv₀))

lemma spectral_centers_at_radius {V : Type uV3} [DecidableEq V]
    (Y : V → E) (u v : Fin (Module.finrank ℝ E) → V)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (T : E →ₗ[ℝ] E) (hT : ∀i, T (b i) = Y (u i) - Y (v i))
    {p : ℕ} (hp : 1 ≤ p) (hpd : p ≤ Module.finrank ℝ E)
    {r : ℝ} (hr : 0 < r)
    (hrT : 32 * (Module.finrank ℝ E : ℝ) * r =
      ∑i : Fin (Module.finrank ℝ E) with p - 1 ≤ i.val, T.adjoint.singularValues i ^ 2) :
    ∃ S : Finset V, S ⊆ (univ.image u ∪ univ.image v) ∧ p < S.card ∧
      (∀x ∈ S, ∀y ∈ S, x ≠ y → 2 * Real.sqrt r < ‖Y x - Y y‖) := by
  classical
  let F := univ.image u ∪ univ.image v
  have hd : 0 < Module.finrank ℝ E := lt_of_lt_of_le (by omega) hpd
  have hF : F.Nonempty := ⟨u ⟨0, hd⟩, mem_union_left _ (mem_image.mpr ⟨⟨0, hd⟩, mem_univ _, rfl⟩)⟩
  obtain ⟨S, hSF, hSne, hsep, hcover⟩ := separated_net F hF Y (show 0 ≤ 2 * Real.sqrt r by positivity)
  refine ⟨S, hSF, ?_, hsep⟩
  by_contra! hSp
  obtain ⟨v₀, hv₀⟩ := hSne
  let c : V → V := fun x => if hx : x ∈ F then Classical.choose (hcover x hx) else v₀
  have hcS (x : V) : c x ∈ S := by
    dsimp [c]
    split
    · exact (Classical.choose_spec (hcover _ ‹_›)).1
    · exact hv₀
  have hcclose (x : V) (hx : x ∈ F) : ‖Y x - Y (c x)‖ ^ 2 ≤ 4 * r := by
    have hh := (Classical.choose_spec (hcover x hx)).2
    have he : c x = Classical.choose (hcover x hx) := dite_eq_left hx
    rw [he]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hh 2
    nlinarith [Real.sq_sqrt hr.le]
  have hu (i) : u i ∈ F := mem_union_left _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩)
  have hv (i) : v i ∈ F := mem_union_right _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩)
  let C := b.toBasis.constr ℝ (fun i => Y (c (u i)) - Y (c (v i)))
  let K := Submodule.span ℝ ((fun x => Y x - Y v₀) '' (S : Set V))
  have hCK : LinearMap.range C ≤ K := by
    apply range_le_of_basis b.toBasis
    intro i
    change C (b.toBasis i) ∈ K
    rw [Module.Basis.constr_basis]
    have huK : Y (c (u i)) - Y v₀ ∈ K := Submodule.subset_span ⟨_, hcS _, rfl⟩
    have hvK : Y (c (v i)) - Y v₀ ∈ K := Submodule.subset_span ⟨_, hcS _, rfl⟩
    convert K.sub_mem huK hvK using 1 <;> first | (with_reducible_and_instances rfl) | (abel)
  have hCrank : Module.finrank ℝ (LinearMap.range C) ≤ p - 1 :=
    (Submodule.finrank_mono hCK).trans ((difference_span_rank S Y hv₀).trans (Nat.sub_le_sub_right hSp 1))
  have hlow := rank_approximation T C ((Nat.sub_le p 1).trans hpd) hCrank
  rw [← hrT] at hlow
  have hupp : frobSq (T - C) ≤ 16 * (Module.finrank ℝ E : ℝ) * r := by
    have hpoint (i : Fin (Module.finrank ℝ E)) : ‖(T - C) (b i)‖ ^ 2 ≤ 16 * r := by
      rw [LinearMap.sub_apply, hT]
      change ‖(Y (u i) - Y (v i)) - C (b.toBasis i)‖ ^ 2 ≤ _
      rw [Module.Basis.constr_basis]
      have heq : (Y (u i) - Y (v i)) - (Y (c (u i)) - Y (c (v i))) =
          (Y (u i) - Y (c (u i))) - (Y (v i) - Y (c (v i))) := by abel
      rw [heq]
      have hh := norm_sub_sq_le_twice (Y (u i) - Y (c (u i))) (Y (v i) - Y (c (v i)))
      linarith [hcclose (u i) (hu i), hcclose (v i) (hv i)]
    rw [frobSq_eq_sum b]
    calc
      _ ≤ ∑i : Fin (Module.finrank ℝ E), (16 * r) := sum_le_sum (fun i _ => hpoint i)
      _ = _ := by simp <;> ring
  have hdr : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast hd
  nlinarith [mul_pos hdr hr]

private lemma tail_split {d : ℕ} (s : Fin d → ℝ) (p : ℕ) :
    tail s p = block s p + tail s (2*p) := by
  classical
  have hh := sum_filter_add_sum_filter_not (univ.filter (fun i : Fin d => p ≤ i.val + 1))
    (fun i => i.val + 1 < 2*p) s
  have heq : (univ.filter (fun i : Fin d => p ≤ i.val+1)).filter (fun i => ¬i.val+1 < 2*p) =
      univ.filter (fun i : Fin d => 2*p ≤ i.val+1) := by
    ext i
    simp only [mem_filter, mem_univ, true_and]
    omega
  rw [heq] at hh
  simpa only [filter_filter, tail, block] using hh.symm

private lemma block_sq_le {d : ℕ} (s : Fin d → ℝ) (p : ℕ) :
    block s p ^ 2 ≤ (p : ℝ) * tail (fun i => s i ^ 2) p := by
  classical
  let B := univ.filter (fun i : Fin d => p ≤ i.val+1 ∧ i.val+1 < 2*p)
  have hcard : B.card ≤ p := by
    have hh : B.card ≤ (range p).card := by
      apply card_le_card_of_injOn (fun i : Fin d => i.val+1-p)
      · intro i hi
        have h := (mem_filter.mp hi).2
        exact mem_range.mpr (by dsimp; omega)
      · intro i hi j hj hij
        have hi' := (mem_filter.mp hi).2
        have hj' := (mem_filter.mp hj).2
        apply Fin.ext
        dsimp at hij
        omega
    simpa using hh
  have hsum : (∑i ∈ B, s i ^ 2) ≤ tail (fun i => s i ^ 2) p := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro i hi; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2.1⟩
    · intro i hi hn; positivity
  have hcs := sum_mul_sq_le_sq_mul_sq B s (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, nsmul_eq_mul, mul_one] at hcs
  calc
    _ ≤ (∑i ∈ B, s i ^ 2) * (B.card : ℝ) := hcs
    _ ≤ tail (fun i => s i ^ 2) p * (p : ℝ) :=
      mul_le_mul hsum (by exact_mod_cast hcard) (by positivity)
        (sum_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := mul_comm _ _

lemma dyadic_tail_selection {d p₀ L : ℕ} (s : Fin d → ℝ)
    (hs : ∀i, 0 ≤ s i) (_hp₀ : 1 ≤ p₀) (hL : 0 < L)
    (hcover : d < 2^L*p₀) (hpositive : 0 < tail s p₀) :
    ∃ p : ℕ, p₀ ≤ p ∧ p ≤ d ∧
      tail s p₀ ^ 2 ≤ (L : ℝ)^2 * ((p : ℝ) * tail (fun i => s i ^ 2) p) := by
  classical
  let p : ℕ → ℕ := fun j => 2^j*p₀
  let M : ℕ → ℝ := fun j => (p j : ℝ) * tail (fun i => s i ^ 2) (p j)
  obtain ⟨j, hj, hmax⟩ := exists_max_image (range L) M (nonempty_range_iff.mpr (ne_of_gt hL))
  have hM : 0 ≤ M j := mul_nonneg (Nat.cast_nonneg _) (sum_nonneg (fun _ _ => sq_nonneg _))
  have hzero : tail s (p L) = 0 := by
    apply sum_eq_zero
    intro i hi
    have hh := (mem_filter.mp hi).2
    dsimp [p] at hh
    omega
  have hpnext (i : ℕ) : p (i+1) = 2*p i := by dsimp [p]; rw [pow_succ]; ring
  have hsplit (i : ℕ) : tail s (p i) - tail s (p (i+1)) = block s (p i) := by
    rw [hpnext, tail_split s (p i)]
    ring
  have hsum : (∑i ∈ range L, block s (p i)) = tail s p₀ := by
    conv_lhs => enter [2, i]; rw [← hsplit]
    rw [sum_range_sub', hzero]
    simp [p]
  have hbound (i : ℕ) (hi : i ∈ range L) : block s (p i) ≤ Real.sqrt (M j) := by
    have hh := (block_sq_le s (p i)).trans (hmax i hi)
    have hn : 0 ≤ block s (p i) := sum_nonneg (fun i _ => hs i)
    nlinarith [Real.sq_sqrt hM, Real.sqrt_nonneg (M j)]
  have htotal : tail s p₀ ≤ (L : ℝ) * Real.sqrt (M j) := by
    rw [← hsum]
    calc
      _ ≤ ∑i ∈ range L, Real.sqrt (M j) := sum_le_sum hbound
      _ = _ := by simp
  have hsq : tail s p₀ ^ 2 ≤ (L : ℝ)^2 * M j := by
    have hh := pow_le_pow_left₀ hpositive.le htotal 2
    rw [mul_pow, Real.sq_sqrt hM] at hh
    exact hh
  have hpd : p j ≤ d := by
    by_contra! hpd
    have hzero : tail (fun i => s i ^ 2) (p j) = 0 := by
      apply sum_eq_zero
      intro i hi
      have hh := (mem_filter.mp hi).2
      omega
    dsimp [M] at hsq
    rw [hzero, mul_zero, mul_zero] at hsq
    nlinarith
  refine ⟨p j, ?_, hpd, hsq⟩
  have hpow : 1 ≤ 2^j := Nat.one_le_pow _ _ (by omega)
  simpa only [one_mul, p] using (Nat.mul_le_mul_right p₀ hpow)

lemma singular_tail_selection {d : ℕ} (hd : 0 < d) (s : Fin d → ℝ)
    (hs : ∀i, 0 ≤ s i) {a τ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hτ : 0 < τ)
    (htrace : τ ≤ ∑i, s i) (hfrob : a * d * (∑i, s i ^ 2) ≤ τ ^ 2) :
    ∃ p L : ℕ, a * d / 16 < p ∧ p ≤ d ∧ 0 < L ∧
      (L : ℝ) ≤ 5 + Real.logb 2 (1/a) ∧
      9 * τ ^ 2 ≤ 16 * (L : ℝ)^2 * ((p : ℝ) * tail (fun i => s i ^ 2) p) := by
  classical
  let f := ⌊a * d / 16⌋₊
  let p₀ := f+1
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have had : 0 ≤ a * d / 16 := by positivity
  have hf : (f : ℝ) ≤ a * d / 16 := Nat.floor_le had
  have hp₀ : a * d / 16 < (p₀ : ℝ) := by simpa only [p₀, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (a*d/16)
  have hp₀pos : 1 ≤ p₀ := by dsimp [p₀]; omega
  have hp₀d : p₀ ≤ d := by
    have hf' : (f : ℝ) < d := by nlinarith
    have hfn : f < d := by exact_mod_cast hf'
    dsimp [p₀]; omega
  let I := univ.filter (fun i : Fin d => i.val < f)
  have hcard : I.card ≤ f := by
    have hh : I.card ≤ (range f).card := by
      apply card_le_card_of_injOn (fun i : Fin d => i.val)
      · intro i hi; exact mem_range.mpr (mem_filter.mp hi).2
      · intro i hi j hj hij; exact Fin.ext hij
    simpa using hh
  have hhead : ∑i ∈ I, s i ≤ τ/4 := by
    have hcs := sum_mul_sq_le_sq_mul_sq I s (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, sum_const, nsmul_eq_mul, mul_one] at hcs
    have hsum : (∑i ∈ I, s i ^ 2) ≤ ∑i, s i ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i hi hn => sq_nonneg _)
    have hcard' : (I.card : ℝ) ≤ a*d/16 := (by exact_mod_cast hcard : (I.card : ℝ) ≤ f).trans hf
    have hupp := mul_le_mul hsum hcard' (Nat.cast_nonneg _) (sum_nonneg (fun _ _ => sq_nonneg _))
    have hheadn : 0 ≤ ∑i ∈ I, s i := sum_nonneg (fun i _ => hs i)
    nlinarith
  have hsplit : (∑i ∈ I, s i) + tail s p₀ = ∑i, s i := by
    have hh := sum_filter_add_sum_filter_not univ (fun i : Fin d => i.val < f) s
    have heq : univ.filter (fun i : Fin d => ¬i.val < f) =
        univ.filter (fun i : Fin d => p₀ ≤ i.val+1) := by
      ext i
      simp only [mem_filter, mem_univ, true_and]
      dsimp [p₀]
      omega
    rw [heq] at hh
    exact hh
  have htail : 3*τ/4 ≤ tail s p₀ := by linarith
  let q := d / p₀
  let L := q.log2 + 1
  have hq : q ≠ 0 := by
    have hqp : 0 < q := Nat.div_pos hp₀d (by omega)
    omega
  have hL : 0 < L := by dsimp [L]; omega
  have hcover : d < 2^L*p₀ := by
    have hh : q < 2^L := (Nat.log2_lt hq).mp (by dsimp [L]; omega)
    exact (Nat.div_lt_iff_lt_mul (by omega)).mp hh
  have hp₀r : (0 : ℝ) < p₀ := by exact_mod_cast (show 0 < p₀ by omega)
  have hqreal : (q : ℝ) ≤ 16/a := by
    have hh : (q : ℝ) * p₀ ≤ d := by exact_mod_cast (Nat.div_mul_le_self d p₀)
    have hqn : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    apply (le_div_iff₀ ha).mpr
    nlinarith
  have hlog : (L : ℝ) ≤ 5 + Real.logb 2 (1/a) := by
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (Nat.pos_of_ne_zero hq)
    have hmono := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hqpos (by positivity : (0 : ℝ) < 16/a)).mpr hqreal
    have hlogq := Real.log2_le_logb q
    have hlog16 : Real.logb 2 (16/a) = 4 + Real.logb 2 (1/a) := by
      rw [show (16 : ℝ)/a = 2^4*(1/a) by ring, Real.logb_mul (by norm_num) (ne_of_gt (by positivity : (0 : ℝ) < 1/a)), Real.logb_pow]
      norm_num
    rw [hlog16] at hmono
    dsimp [L]
    push_cast
    linarith
  obtain ⟨p, hpp, hpd, hpbig⟩ := dyadic_tail_selection s hs hp₀pos hL hcover (by linarith)
  refine ⟨p, L, hp₀.trans_le (by exact_mod_cast hpp), hpd, hL, hlog, ?_⟩
  have htailn : 0 ≤ tail s p₀ := by linarith
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 3*τ/4) htail 2
  nlinarith

lemma trace_sq_le_frobSq (T : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E T ^ 2 ≤ (Module.finrank ℝ E : ℝ) * frobSq T := by
  let b := stdOrthonormalBasis ℝ E
  have hh := trace_bound T b
  have hn : 0 ≤ ∑i, ‖T (b i)‖ := sum_nonneg (fun _ _ => norm_nonneg _)
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hh 2
  have hcs := sum_mul_sq_le_sq_mul_sq univ (fun i => ‖T (b i)‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hcs
  rw [← frobSq_eq_sum b] at hcs
  rw [sq_abs] at hsq
  exact hsq.trans (hcs.trans_eq (mul_comm _ _))

lemma spectral_packing_log {V : Type uV4} [DecidableEq V]
    (Y : V → E) (u v : Fin (Module.finrank ℝ E) → V)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (T : E →ₗ[ℝ] E) (hT : ∀i, T (b i) = Y (u i) - Y (v i))
    {a : ℝ} (ha : 0 < a) (htrace : 0 < |LinearMap.trace ℝ E T|)
    (hassume : a * Module.finrank ℝ E * frobSq T ≤ LinearMap.trace ℝ E T ^ 2) :
    a ≤ 1 ∧ ∃ S : Finset V, ∃ r : ℝ, 0 < r ∧
      S ⊆ (univ.image u ∪ univ.image v) ∧ 2 ≤ S.card ∧
      a * Module.finrank ℝ E / 16 ≤ S.card ∧
      9 * LinearMap.trace ℝ E T ^ 2 ≤
        512 * Module.finrank ℝ E * (5 + Real.logb 2 (1/a))^2 * (S.card * r) ∧
      (∀x ∈ S, ∀y ∈ S, x ≠ y → 2 * Real.sqrt r < ‖Y x - Y y‖) := by
  classical
  let d := Module.finrank ℝ E
  let τ := |LinearMap.trace ℝ E T|
  have htsq : τ ^ 2 = LinearMap.trace ℝ E T ^ 2 := sq_abs _
  have htpos : 0 < τ ^ 2 := sq_pos_of_pos htrace
  have htraceF := trace_sq_le_frobSq T
  have hdn : (0 : ℝ) < d := by
    have hf := frobSq_nonneg T
    dsimp [d]
    by_contra! hn
    have hz : (Module.finrank ℝ E : ℝ) = 0 := le_antisymm hn (Nat.cast_nonneg _)
    rw [hz, zero_mul] at htraceF
    nlinarith
  have hd : 0 < d := by exact_mod_cast hdn
  have hfpos : 0 < frobSq T := by nlinarith
  have ha1 : a ≤ 1 := by
    have hh : 0 < (d : ℝ) * frobSq T := mul_pos hdn hfpos
    have hh' : a * ((d : ℝ) * frobSq T) ≤ (d : ℝ) * frobSq T := by
      calc
        _ = a * d * frobSq T := by ring
        _ ≤ LinearMap.trace ℝ E T ^ 2 := hassume
        _ ≤ _ := htraceF
    exact (mul_le_mul_iff_left₀ hh).mp (by simpa only [mul_comm, one_mul] using hh')
  let s := fun i : Fin d => T.adjoint.singularValues i
  have hs (i : Fin d) : 0 ≤ s i := T.adjoint.singularValues_nonneg i
  have hsum : τ ≤ ∑i, s i := by
    simpa only [trace_adjoint] using trace_le_singular_sum T.adjoint
  have hsq : a * d * (∑i, s i ^ 2) ≤ τ ^ 2 := by
    rw [← frobSq_eq_singular_sum T.adjoint, frobSq_adjoint, htsq]
    exact hassume
  obtain ⟨p, L, hpmin, hpd, hL, hlog, hpbig⟩ := singular_tail_selection hd s hs ha ha1 htrace hsum hsq
  have hpp : 1 ≤ p := by
    have hpp' : (0 : ℝ) < p := lt_of_le_of_lt (by positivity) hpmin
    have : 0 < p := by exact_mod_cast hpp'
    omega
  let tailVal := tail (fun i => s i ^ 2) p
  have htailpos : 0 < tailVal := by
    have hn : 0 ≤ tailVal := sum_nonneg (fun _ _ => sq_nonneg _)
    by_contra! hh
    have hz : tailVal = 0 := le_antisymm hh hn
    change 9*τ^2 ≤ 16*(L:ℝ)^2*((p:ℝ)*tailVal) at hpbig
    rw [hz, mul_zero, mul_zero] at hpbig
    nlinarith
  let r := tailVal / (32*d)
  have hr : 0 < r := div_pos htailpos (by positivity)
  have hrt : 32*(d:ℝ)*r = tailVal := by dsimp [r]; field_simp
  have heq : tailVal =
      ∑i : Fin d with p-1 ≤ i.val, T.adjoint.singularValues i ^ 2 := by
    unfold tailVal tail
    apply sum_congr
    · ext i
      simp only [mem_filter, mem_univ, true_and]
      omega
    · intro i hi; rfl
  obtain ⟨S, hSF, hpS, hsep⟩ := spectral_centers_at_radius Y u v b T hT hpp hpd hr (hrt.trans heq)
  have hpSr : (p : ℝ) ≤ S.card := by exact_mod_cast hpS.le
  have hSr : 0 ≤ (S.card : ℝ)*r := mul_nonneg (Nat.cast_nonneg _) hr.le
  have hpr : (p : ℝ)*r ≤ S.card*r := mul_le_mul_of_nonneg_right hpSr hr.le
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hlogn : 0 ≤ 5+Real.logb 2 (1/a) := hLr.le.trans hlog
  have hLsq := pow_le_pow_left₀ hLr.le hlog 2
  refine ⟨ha1, S, r, hr, hSF, by omega, hpmin.le.trans hpSr, ?_, hsep⟩
  have hpbig' : 9*τ^2 ≤ 512*(d:ℝ)*(L:ℝ)^2*((p:ℝ)*r) := by
    change 9*τ^2 ≤ 16*(L:ℝ)^2*((p:ℝ)*tailVal) at hpbig
    rw [← hrt] at hpbig
    convert hpbig using 1 <;> first | rfl | ring
  rw [← htsq]
  calc
    _ ≤ 512*(d:ℝ)*(L:ℝ)^2*((p:ℝ)*r) := hpbig'
    _ ≤ 512*(d:ℝ)*(L:ℝ)^2*(S.card*r) :=
      mul_le_mul_of_nonneg_left hpr (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLsq (by positivity)) hSr

lemma logarithmic_power_bound {a ε : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hε : 0 < ε) (hε1 : ε < 1/3) :
    ε^2 * a^ε * (5 + Real.logb 2 (1/a))^2 ≤ 16 := by
  let t := Real.log (1/a)
  have ht : 0 ≤ t := Real.log_nonneg (by exact (one_le_div ha).mpr ha1)
  have htlog : t = - Real.log a := by dsimp [t]; rw [Real.log_div (by norm_num) ha.ne']; simp
  have hlog2 : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog : 5+Real.logb 2 (1/a) ≤ 5+2*t := by
    dsimp [Real.logb]
    have hh : t / Real.log 2 ≤ 2*t := (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr (by nlinarith)
    linarith
  have hlogn : 0 ≤ 5+Real.logb 2 (1/a) := by
    have hh := Real.logb_nonneg (by norm_num : (1:ℝ)<2) ((one_le_div ha).mpr ha1)
    linarith
  let z := ε*t/2
  have hz : 0 ≤ z := by dsimp [z] <;> positivity
  have hexple : Real.exp (-z) ≤ 1 := by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
  have he1 : Real.exp (-1) ≤ 1/2 := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      (inv_anti₀ (by norm_num : (0:ℝ)<2) (by linarith [Real.add_one_le_exp 1] : (2:ℝ) ≤ Real.exp 1))
  have hzbound : z * Real.exp (-z) ≤ 1/2 := (Real.mul_exp_neg_le_exp_neg_one z).trans he1
  have hmain : ε*(5+Real.logb 2 (1/a))*Real.exp (-z) ≤ 4 := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hε.le) (Real.exp_pos (-z)).le
    have h5 := mul_le_mul_of_nonneg_left hexple (show 0 ≤ 5*ε by positivity)
    dsimp [z] at hzbound
    nlinarith
  have heq : Real.exp (-z)^2 = a^ε := by
    rw [← Real.exp_nat_mul, Real.rpow_def_of_pos ha]
    congr 1
    dsimp [z]
    rw [htlog]
    ring
  have hn : 0 ≤ ε*(5+Real.logb 2 (1/a))*Real.exp (-z) := by positivity
  have hh := pow_le_pow_left₀ hn hmain 2
  rw [mul_pow, mul_pow, heq] at hh
  nlinarith

lemma spectral_packing_power {V : Type uV5} [DecidableEq V]
    (Y : V → E) (u v : Fin (Module.finrank ℝ E) → V)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (T : E →ₗ[ℝ] E) (hT : ∀i, T (b i) = Y (u i) - Y (v i))
    {a ε : ℝ} (ha : 0 < a) (htrace : 0 < |LinearMap.trace ℝ E T|)
    (hassume : a * Module.finrank ℝ E * frobSq T ≤ LinearMap.trace ℝ E T ^ 2)
    (hε : 0 < ε) (hε1 : ε < 1/3) :
    a ≤ 1 ∧ ∃ S : Finset V, ∃ r : ℝ, 0 < r ∧
      S ⊆ (univ.image u ∪ univ.image v) ∧ 2 ≤ S.card ∧
      ε^2 * a * Module.finrank ℝ E ≤ 1024 * S.card ∧
      ε^2 * a^ε * LinearMap.trace ℝ E T ^ 2 ≤
        1024 * Module.finrank ℝ E * (S.card * r) ∧
      (∀x ∈ S, ∀y ∈ S, x ≠ y → 2 * Real.sqrt r < ‖Y x - Y y‖) := by
  obtain ⟨ha1, S, r, hr, hSF, hS2, hcard, hlog, hsep⟩ :=
    spectral_packing_log Y u v b T hT ha htrace hassume
  have he2 : ε^2 ≤ 64 := by nlinarith
  have hd : 0 ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hSr : 0 ≤ (S.card : ℝ)*r := mul_nonneg (Nat.cast_nonneg _) hr.le
  have hpow : 0 ≤ ε^2 * a^ε := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ha.le _)
  have hh := mul_le_mul_of_nonneg_left hlog hpow
  have hb := mul_le_mul_of_nonneg_right (logarithmic_power_bound ha ha1 hε hε1)
    (show 0 ≤ 512*(Module.finrank ℝ E : ℝ)*(S.card*r) by positivity)
  refine ⟨ha1, S, r, hr, hSF, hS2, ?_, ?_, hsep⟩
  · have hc : a * Module.finrank ℝ E ≤ 16 * S.card := by linarith
    have hh := mul_le_mul_of_nonneg_left hc (sq_nonneg ε)
    have hb := mul_le_mul_of_nonneg_right he2 (show 0 ≤ 16*(S.card:ℝ) by positivity)
    nlinarith
  · have h9 : 9 * (ε^2 * a^ε * LinearMap.trace ℝ E T ^ 2) ≤
        8192 * Module.finrank ℝ E * (S.card * r) := by
      calc
        _ ≤ ε^2 * a^ε *
          (512 * Module.finrank ℝ E * (5 + Real.logb 2 (1/a))^2 * (S.card*r)) := by
            nlinarith only [hh]
        _ = (ε^2 * a^ε * (5 + Real.logb 2 (1/a))^2) *
            (512 * Module.finrank ℝ E * (S.card*r)) := by ring
        _ ≤ _ := by nlinarith only [hb]
    have hn : 0 ≤ (Module.finrank ℝ E : ℝ) * (S.card*r) := mul_nonneg hd hSr
    nlinarith

theorem spectral_packing_coordinates {V : Type uV6} {ι : Type uι4} {η : Type uη} [DecidableEq V]
    [Fintype ι] [Fintype η] [DecidableEq ι] [DecidableEq η]
    (Y : V → EuclideanSpace ℝ η) (u v : ι → V)
    (j : ι → η) (hj : Function.Injective j) {a ε : ℝ}
    (ha : 0 < a) (hε : 0 < ε) (hε1 : ε < 1/3)
    (hpos : 0 < (∑i, (Y (u i) - Y (v i)).ofLp (j i))^2)
    (hbound : a * Fintype.card ι * (∑i, ‖Y (u i)-Y (v i)‖^2) ≤
      (∑i, (Y (u i)-Y (v i)).ofLp (j i))^2) :
    a ≤ 1 ∧ ∃ S : Finset V, ∃ r : ℝ, 0 < r ∧
      S ⊆ (univ.image u ∪ univ.image v) ∧ 2 ≤ S.card ∧
      ε^2 * a * Fintype.card ι ≤ 1024 * S.card ∧
      ε^2 * a^ε * (∑i, (Y (u i)-Y (v i)).ofLp (j i))^2 ≤
        1024 * Fintype.card ι * (S.card*r) ∧
      (∀x ∈ S, ∀y ∈ S, x ≠ y → 2 * Real.sqrt r < ‖Y x-Y y‖) := by
  classical
  let Y' : V → EuclideanSpace ℝ ι := fun x => WithLp.toLp 2 (fun i => (Y x).ofLp (j i))
  let b₀ := EuclideanSpace.basisFun ι ℝ
  let T := b₀.toBasis.constr ℝ (fun i => Y' (u i)-Y' (v i))
  have hT₀ (i : ι) : T (b₀ i) = Y' (u i)-Y' (v i) :=
    b₀.toBasis.constr_basis ℝ _ i
  have htr : LinearMap.trace ℝ (EuclideanSpace ℝ ι) T =
      ∑i, (Y (u i)-Y (v i)).ofLp (j i) := by
    rw [LinearMap.trace_eq_sum_inner _ b₀]
    apply sum_congr rfl
    intro i hi
    rw [hT₀, EuclideanSpace.basisFun_inner]
    rfl
  have hn (x y : V) : ‖Y' x-Y' y‖^2 ≤ ‖Y x-Y y‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq]
    change (∑i, ‖(Y x-Y y).ofLp (j i)‖^2) ≤ ∑i, ‖(Y x-Y y).ofLp i‖^2
    rw [← sum_image (f := fun i => ‖(Y x-Y y).ofLp i‖^2) hj.injOn]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; positivity)
  have hf : frobSq T ≤ ∑i, ‖Y (u i)-Y (v i)‖^2 := by
    rw [frobSq_eq_sum b₀]
    exact sum_le_sum (fun i _ => by rw [hT₀]; exact hn _ _)
  let e : Fin (Module.finrank ℝ (EuclideanSpace ℝ ι)) ≃ ι :=
    (finCongr finrank_euclideanSpace).trans (Fintype.equivFin ι).symm
  let b := b₀.reindex e.symm
  have hT : ∀i, T (b i) = Y' (u (e i))-Y' (v (e i)) := by
    intro i
    simpa only [b, OrthonormalBasis.reindex_apply, Equiv.symm_symm] using hT₀ (e i)
  have hassume : a * Module.finrank ℝ (EuclideanSpace ℝ ι) * frobSq T ≤
      LinearMap.trace ℝ (EuclideanSpace ℝ ι) T ^ 2 := by
    rw [htr, finrank_euclideanSpace]
    exact (mul_le_mul_of_nonneg_left hf (by positivity)).trans hbound
  have htrace : 0 < |LinearMap.trace ℝ (EuclideanSpace ℝ ι) T| := by
    rw [htr]
    exact abs_pos.mpr (sq_pos_iff.mp hpos)
  obtain ⟨ha1, S, r, hr, hSF, hS2, hcard, hmass, hsep⟩ :=
    spectral_packing_power Y' (u ∘ e) (v ∘ e) b T hT ha htrace hassume hε hε1
  rw [htr, finrank_euclideanSpace] at hmass
  rw [finrank_euclideanSpace] at hcard
  refine ⟨ha1, S, r, hr, ?_, hS2, hcard, hmass, ?_⟩
  · intro x hx
    rcases mem_union.mp (hSF hx) with hh | hh
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hh
      exact mem_union_left _ (mem_image.mpr ⟨e i, mem_univ _, rfl⟩)
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hh
      exact mem_union_right _ (mem_image.mpr ⟨e i, mem_univ _, rfl⟩)
  · intro x hx y hy hxy
    exact (hsep x hx y hy hxy).trans_le ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hn x y))

end
end StrongThinTree.Spectral

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_BagGeometry
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV uI uV2 uV3 uI2 uJ

section
open scoped Classical
open Matrix

namespace StrongThinTree.Geometry
noncomputable section
open Finset
open scoped Classical
variable {V : Type uV} {I : Type uI} [DecidableEq V] [DecidableEq I] {h : ℕ}

omit [DecidableEq V] in

lemma retain_fibers (S : Finset V) (T : Finset I) (f : V → I)
    (hf : ∀u ∈ S, f u ∈ T) (w : I → ℝ) (hw : ∀i ∈ T, 0 < w i)
    {c : ℝ} (hc : 0 < c) :
    ∃J : Finset I, J ⊆ T ∧
      (∀i ∈ J, (S.filter (fun u => f u=i)).Nonempty ∧
        c*w i ≤ ((S.filter (fun u => f u=i)).card : ℝ)) ∧
      (S.card : ℝ)-c*(∑i ∈ T, w i) ≤ ∑i ∈ J, ((S.filter (fun u => f u=i)).card : ℝ) := by
  let J := T.filter (fun i => c*w i ≤ ((S.filter (fun u => f u=i)).card : ℝ))
  have hsum : (∑i ∈ T, ((S.filter (fun u => f u=i)).card : ℝ)) = S.card := by
    rw [←Nat.cast_sum]
    congr 1
    exact sum_card_fiberwise_eq_card_filter S T f |>.trans (by
      congr 1
      exact filter_eq_self.mpr hf)
  refine ⟨J,filter_subset _ _,?_,?_⟩
  · intro i hi
    obtain ⟨hi,hci⟩ := mem_filter.mp hi
    refine ⟨card_pos.mp ?_,hci⟩
    have hh := mul_pos hc (hw i hi)
    have : (0:ℝ) < (S.filter (fun u => f u=i)).card := hh.trans_le hci
    exact_mod_cast this
  · have hbound : ∑i ∈ T, ((S.filter (fun u => f u=i)).card : ℝ) ≤
        (∑i ∈ T, if i ∈ J then ((S.filter (fun u => f u=i)).card : ℝ) else 0)+c*(∑i ∈ T, w i) := by
      rw [mul_sum,←sum_add_distrib]
      apply sum_le_sum
      intro i hi
      by_cases hiJ : i ∈ J
      · rw [ite_eq_left hiJ]
        linarith [mul_pos hc (hw i hi)]
      · rw [ite_eq_right hiJ,zero_add]
        exact le_of_lt (lt_of_not_ge (fun hh => hiJ (mem_filter.mpr ⟨hi,hh⟩)))
    rw [hsum] at hbound
    have he : (∑i ∈ T, if i ∈ J then ((S.filter (fun u => f u=i)).card : ℝ) else 0) =
        ∑i ∈ J, ((S.filter (fun u => f u=i)).card : ℝ) := by
      rw [←sum_filter]
      congr 1
      exact filter_mem_eq_inter.trans (inter_eq_right.mpr (filter_subset _ _))
    rw [he] at hbound
    linarith

end
end StrongThinTree.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Capture
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
open scoped Classical
variable {n m : ℕ} (H : Hierarchy n) (G : MultiGraph n m)

lemma boundary_owner_unique {A B : Finset (Fin n)} {u v : Fin n}
    (hA : A ∈ H.nodes) (hB : B ∈ H.nodes) (hAr : A ≠ univ) (hBr : B ≠ univ)
    (huA : u ∈ A) (huB : u ∈ B) (hvA : v ∉ A) (hvB : v ∉ B)
    (hvPA : v ∈ H.parent A) (hvPB : v ∈ H.parent B) : A = B := by
  rcases H.laminar A hA B hB with hAB | hBA | hdis
  · by_contra hne
    have hp := H.parent_minimal A hA hAr B hB (Finset.ssubset_iff_subset_ne.mpr ⟨hAB,hne⟩)
    exact hvB (hp hvPA)
  · by_contra hne
    have hp := H.parent_minimal B hB hBr A hA (Finset.ssubset_iff_subset_ne.mpr ⟨hBA,Ne.symm hne⟩)
    exact hvA (hp hvPB)
  · exact (Finset.disjoint_left.mp hdis huA huB).elim

lemma parentBoundary_multiplicity (T : Finset (Finset (Fin n)))
    (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ) (e : Fin m) :
    (T.filter (fun t => e ∈ H.parentBoundary G t)).card ≤ 2 := by
  let S := T.filter (fun t => e ∈ H.parentBoundary G t)
  let L := S.filter (fun t => G.left e ∈ t)
  let R := S.filter (fun t => G.right e ∈ t)
  have hL : L.card ≤ 1 := by
    apply card_le_one.mpr
    intro A hA B hB
    obtain ⟨hA,hlA⟩ := mem_filter.mp hA
    obtain ⟨hB,hlB⟩ := mem_filter.mp hB
    obtain ⟨hAT,heA⟩ := mem_filter.mp hA
    obtain ⟨hBT,heB⟩ := mem_filter.mp hB
    obtain ⟨hePA,hcutA⟩ := mem_filter.mp heA
    obtain ⟨hePB,hcutB⟩ := mem_filter.mp heB
    have hrA : G.right e ∉ A := by rcases hcutA with hh | hh; exact hh.2; exact (hh.2 hlA).elim
    have hrB : G.right e ∉ B := by rcases hcutB with hh | hh; exact hh.2; exact (hh.2 hlB).elim
    exact H.boundary_owner_unique (hT hAT) (hT hBT) (hroot A hAT) (hroot B hBT)
      hlA hlB hrA hrB ((G.mem_inducedEdges _ _).mp hePA).2 ((G.mem_inducedEdges _ _).mp hePB).2
  have hR : R.card ≤ 1 := by
    apply card_le_one.mpr
    intro A hA B hB
    obtain ⟨hA,hrA⟩ := mem_filter.mp hA
    obtain ⟨hB,hrB⟩ := mem_filter.mp hB
    obtain ⟨hAT,heA⟩ := mem_filter.mp hA
    obtain ⟨hBT,heB⟩ := mem_filter.mp hB
    obtain ⟨hePA,hcutA⟩ := mem_filter.mp heA
    obtain ⟨hePB,hcutB⟩ := mem_filter.mp heB
    have hlA : G.left e ∉ A := by rcases hcutA with hh | hh; exact (hh.2 hrA).elim; exact hh.2
    have hlB : G.left e ∉ B := by rcases hcutB with hh | hh; exact (hh.2 hrB).elim; exact hh.2
    exact H.boundary_owner_unique (hT hAT) (hT hBT) (hroot A hAT) (hroot B hBT)
      hrA hrB hlA hlB ((G.mem_inducedEdges _ _).mp hePA).1 ((G.mem_inducedEdges _ _).mp hePB).1
  have hsub : S ⊆ L∪R := by
    intro A hA
    have hc := (mem_filter.mp (mem_filter.mp hA).2).2
    rcases hc with hh | hh
    · exact mem_union_left _ (mem_filter.mpr ⟨hA,hh.1⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hA,hh.1⟩)
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (by omega))

lemma subset_boundary_multiplicity (T : Finset (Finset (Fin n)))
    (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
    (F : Finset (Fin n) → Finset (Fin m)) (hF : ∀t ∈ T, F t ⊆ H.parentBoundary G t) :
    (∑t ∈ T, (F t).card) ≤ 2*(T.biUnion F).card := by
  have hdouble : (∑t ∈ T, (F t).card) =
      ∑e ∈ T.biUnion F, (T.filter (fun t => e ∈ F t)).card := by
    simp only [card_eq_sum_ones,sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro t ht
    simp only [←sum_filter]
    congr 1
    ext e
    simp only [mem_filter,mem_biUnion]
    exact ⟨fun hh => ⟨⟨t,ht,hh⟩,hh⟩,fun hh => hh.2⟩
  rw [hdouble]
  have heq : 2*(T.biUnion F).card = ∑_e ∈ T.biUnion F, 2 := by simp [mul_comm]
  rw [heq]
  apply sum_le_sum
  intro e he
  apply le_trans (card_le_card (show T.filter (fun t => e ∈ F t) ⊆
      T.filter (fun t => e ∈ H.parentBoundary G t) from by
    intro t ht
    obtain ⟨ht,he⟩ := mem_filter.mp ht
    exact mem_filter.mpr ⟨ht,hF t ht he⟩))
  exact H.parentBoundary_multiplicity G T hT hroot e

end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Density
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uT uE uI uI2 uA uB

section
open scoped Classical
open Matrix

namespace StrongThinTree.BagDensity
noncomputable section
open Finset
open scoped Classical
variable {T : Type uT} {E : Type uE} [DecidableEq E]

omit [DecidableEq E] in
lemma sum_square_bound (F : Finset E) (a : E → ℝ) {c : ℝ}
    (hc : ∀e ∈ F, (a e)^2 ≤ c) : (∑e ∈ F, a e)^2 ≤ c*(F.card : ℝ)^2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq F (fun _ => (1:ℝ)) a
  have hs : (∑e ∈ F, (a e)^2) ≤ (F.card : ℝ)*c := by simpa using sum_le_sum hc
  simp only [one_pow,sum_const,nsmul_eq_mul,mul_one,one_mul] at hcs
  have hm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg F.card : (0:ℝ) ≤ _)
  nlinarith

omit [DecidableEq E] in
lemma local_density (O F : Finset E) (a d : E → ℝ) {α γ c₁ c₂ : ℝ}
    (hF : F ⊆ O) (hFn : F.Nonempty) (hα : 0 < α) (hγ : 0 < γ)
    (hd : ∀e ∈ O, 0 ≤ d e) (hmax : ∀e ∈ F, (a e)^2 ≤ 4*c₁)
    (hmin : ∀e ∈ F, c₂/4 ≤ d e)
    (hbad : α*(O.card : ℝ)*(∑e ∈ O, d e) ≤ (∑e ∈ O, a e)^2)
    (hdom : γ*(∑e ∈ O, a e)^2 ≤ (∑e ∈ F, a e)^2) :
    α*γ*(O.card : ℝ)*c₂ ≤ 16*c₁*F.card := by
  have hFc : (0:ℝ) < F.card := by exact_mod_cast card_pos.mpr hFn
  have hOc : (0:ℝ) ≤ O.card := Nat.cast_nonneg _
  have hsum : (F.card : ℝ)*(c₂/4) ≤ ∑e ∈ O, d e := by
    calc
      _ = ∑_e ∈ F, c₂/4 := by simp
      _ ≤ ∑e ∈ F, d e := sum_le_sum hmin
      _ ≤ ∑e ∈ O, d e := sum_le_sum_of_subset_of_nonneg hF (fun e he _ => hd e he)
  have hh1 := mul_le_mul_of_nonneg_left hsum (show 0 ≤ γ*α*(O.card : ℝ) by positivity)
  have hh2 := mul_le_mul_of_nonneg_left hbad hγ.le
  have hu := sum_square_bound F a hmax
  apply (mul_le_mul_iff_right₀ hFc).mp
  nlinarith

lemma family_density (Ts : Finset T) (O F : T → Finset E) (a d : E → ℝ)
    {α γ c₁ c₂ : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hc : 0 ≤ c₁)
    (hF : ∀t ∈ Ts, F t ⊆ O t) (hFn : ∀t ∈ Ts, (F t).Nonempty)
    (hd : ∀t ∈ Ts, ∀e ∈ O t, 0 ≤ d e)
    (hmax : ∀t ∈ Ts, ∀e ∈ F t, (a e)^2 ≤ 4*c₁)
    (hmin : ∀t ∈ Ts, ∀e ∈ F t, c₂/4 ≤ d e)
    (hbad : ∀t ∈ Ts, α*((O t).card : ℝ)*(∑e ∈ O t, d e) ≤ (∑e ∈ O t, a e)^2)
    (hdom : ∀t ∈ Ts, γ*(∑e ∈ O t, a e)^2 ≤ (∑e ∈ F t, a e)^2)
    (hmult : (∑t ∈ Ts, (F t).card) ≤ 2*(Ts.biUnion F).card) :
    (α*γ/32)*(∑t ∈ Ts, ((O t).card : ℝ))*c₂ ≤ c₁*(Ts.biUnion F).card ∧
    (∑t ∈ Ts, (∑e ∈ F t, a e)^2/((O t).card : ℝ)) ≤ 8*c₁*(Ts.biUnion F).card := by
  have hcast : (∑t ∈ Ts, ((F t).card : ℝ)) ≤ 2*(Ts.biUnion F).card := by exact_mod_cast hmult
  constructor
  · have hh := sum_le_sum (fun t ht => local_density (O t) (F t) a d
      (hF t ht) (hFn t ht) hα hγ (hd t ht) (hmax t ht) (hmin t ht) (hbad t ht) (hdom t ht))
    simp only [←mul_sum,←sum_mul] at hh
    have hm := mul_le_mul_of_nonneg_left hcast (show 0 ≤ 16*c₁ by positivity)
    nlinarith
  · have hu : ∀t ∈ Ts, (∑e ∈ F t, a e)^2/((O t).card : ℝ) ≤ 4*c₁*(F t).card := by
      intro t ht
      have hm : (0:ℝ) < (O t).card := by exact_mod_cast card_pos.mpr ((hFn t ht).mono (hF t ht))
      have hfm : ((F t).card : ℝ) ≤ (O t).card := by exact_mod_cast card_le_card (hF t ht)
      have hs := sum_square_bound (F t) a (hmax t ht)
      apply (div_le_iff₀ hm).mpr
      have hh := mul_le_mul_of_nonneg_left hfm (show 0 ≤ 4*c₁*(F t).card by positivity)
      nlinarith
    have hs := sum_le_sum hu
    rw [←mul_sum] at hs
    have hh := mul_le_mul_of_nonneg_left hcast (show 0 ≤ 4*c₁ by positivity)
    nlinarith

end
end StrongThinTree.BagDensity

namespace StrongThinTree.CaptureNumeric
noncomputable section

lemma thresholds {s a ε C N N' c₁ c₂ b δ R : ℝ}
    (hs : 0 < s) (ha : s ≤ a) (ha1 : a ≤ 1)
    (he : 0 < ε) (he1 : ε ≤ 1/2) (hC : 0 < C)
    (hN : 0 < N) (hN' : 0 < N') (hNle : N' ≤ N)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (_hb : 0 < b) (hδ : 0 < δ)
    (hscale : a*N' = s*N) (hdensity : s*N*c₂ ≤ c₁*N')
    (hcard : a*N'/C ≤ b) (hcard₂ : b ≤ 2*N')
    (hmass : b*δ = a^ε*c₁*N'/C)
    (hsmall : s^ε ≤ 1/(1728*C)) (hR : R ≤ 8*c₁*N') :
    864*s^(1+2*ε)*N ≤ b ∧
    1728*s^(1+2*ε)*c₂*N ≤ δ*b ∧
    s*c₁ ≤ δ ∧ max δ (2*c₂) ≤ 2*c₁/s ∧
    s^ε*R/(6912*C) ≤ δ*b/864 := by
  have ha0 : 0 < a := hs.trans_le ha
  have hs1 : s ≤ 1 := ha.trans ha1
  have hsε : 0 < s^ε := Real.rpow_pos_of_pos hs _
  have haε : 0 < a^ε := Real.rpow_pos_of_pos ha0 _
  have hsε1 : s^ε ≤ 1 := Real.rpow_le_one hs.le hs1 he.le
  have haε1 : a^ε ≤ 1 := Real.rpow_le_one ha0.le ha1 he.le
  have hsale : s^ε ≤ a^ε := Real.rpow_le_rpow hs.le ha he.le
  have hsmall' := (le_div_iff₀ (show 0 < 1728*C by positivity)).mp hsmall
  have hη : s^(1+2*ε) = s*(s^ε)^2 := by
    rw [Real.rpow_add hs,Real.rpow_one]
    congr 1
    rw [mul_comm (2:ℝ) ε,Real.rpow_mul hs.le,Real.rpow_two]
  have hfirst : 864*s^(1+2*ε)*N ≤ b := by
    have hc := (div_le_iff₀ hC).mp hcard
    rw [hscale] at hc
    rw [hη]
    have hh : 864*(s^ε)^2*C ≤ 1 := by nlinarith only [hsmall',mul_nonneg (sub_nonneg.mpr hsε1) (by positivity : 0 ≤ 1728*C*s^ε)]
    have hmul := mul_le_mul_of_nonneg_right hh (show 0 ≤ s*N by positivity)
    apply (mul_le_mul_iff_right₀ hC).mp
    nlinarith only [hmul,hc]
  have hsecond : 1728*s^(1+2*ε)*c₂*N ≤ δ*b := by
    have hh := mul_le_mul_of_nonneg_right hdensity (show 0 ≤ 1728*(s^ε)^2*C by positivity)
    have hh' : 1728*(s^ε)^2*C ≤ a^ε := by
      have hh := mul_le_mul_of_nonneg_right hsmall' hsε.le
      nlinarith only [hh,hsale]
    have hh'' := mul_le_mul_of_nonneg_right hh' (show 0 ≤ c₁*N' by positivity)
    have hm := (eq_div_iff hC.ne').mp hmass
    rw [hη]
    apply (mul_le_mul_iff_right₀ hC).mp
    nlinarith only [hh,hh'',hm]
  have hlower : s*c₁ ≤ δ := by
    have hpow := Real.rpow_le_rpow_of_exponent_ge hs hs1 (show ε ≤ 1-ε by linarith)
    have hex : s = s^ε*s^(1-ε) := by
      rw [←Real.rpow_add hs]
      have heq : ε+(1-ε) = 1 := by ring
      rw [heq,Real.rpow_one]
    have hh : 2*C*s ≤ s^ε := by
      have hc : 2*C*s^(1-ε) ≤ 1 := by nlinarith only [hsmall',mul_le_mul_of_nonneg_left hpow hC.le]
      have hm := mul_le_mul_of_nonneg_left hc hsε.le
      nlinarith only [hm,congrArg (fun x : ℝ => 2*C*x) hex]
    have hh' := mul_le_mul_of_nonneg_right hh (show 0 ≤ c₁*N' by positivity)
    have hh'' := mul_le_mul_of_nonneg_right hsale (show 0 ≤ c₁*N' by positivity)
    have hm := (eq_div_iff hC.ne').mp hmass
    have hbc := mul_le_mul_of_nonneg_right hcard₂ hδ.le
    have hbcC := mul_le_mul_of_nonneg_right hbc hC.le
    apply (mul_le_mul_iff_right₀ (show 0 < 2*C*N' by positivity)).mp
    nlinarith only [hh',hh'',hm,hbcC]
  have hupperδ : δ ≤ c₁/s := by
    have hh := mul_le_mul_of_nonneg_right hcard hδ.le
    have hm := (eq_div_iff hC.ne').mp hmass
    have hc := (div_le_iff₀ hC).mp hcard
    have hhC := mul_le_mul_of_nonneg_right hh hC.le
    have hhA := mul_le_mul_of_nonneg_right haε1 (show 0 ≤ c₁*N' by positivity)
    have hhS := mul_le_mul_of_nonneg_right ha (show 0 ≤ N'*δ by positivity)
    apply (le_div_iff₀ hs).mpr
    apply (mul_le_mul_iff_right₀ hN').mp
    have hcan : (a*N'/C)*δ*C = a*N'*δ := by field_simp
    rw [hcan] at hhC
    nlinarith only [hhC,hm,hhA,hhS]
  have hupperc : c₂ ≤ c₁/s := by
    have hh := mul_le_mul_of_nonneg_left hNle (show 0 ≤ s*c₂ by positivity)
    apply (le_div_iff₀ hs).mpr
    apply (mul_le_mul_iff_right₀ hN').mp
    nlinarith only [hh,hdensity]
  refine ⟨hfirst,hsecond,hlower,max_le ?_ ?_,?_⟩
  · have hh : 0 ≤ c₁/s := by positivity
    rw [mul_div_assoc]
    linarith only [hh,hupperδ]
  · have hh := mul_le_mul_of_nonneg_left hupperc (show (0:ℝ) ≤ 2 by norm_num)
    simpa only [mul_div_assoc] using hh
  · have hh := mul_le_mul_of_nonneg_left hR hsε.le
    have hh' := mul_le_mul_of_nonneg_right hsale (show 0 ≤ 8*c₁*N' by positivity)
    have hm := (eq_div_iff hC.ne').mp hmass
    apply (div_le_iff₀ (show 0 < 6912*C by positivity)).mpr
    nlinarith only [hh,hh',hm]

end
end StrongThinTree.CaptureNumeric

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_CompactCharging
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric compact charging. -/

section

namespace AlgorithmicThinTrees.MetricProfiles.CompactGeometry
noncomputable section
open Finset

section RadialLaws
variable {J : Type*} [Fintype J] [PseudoMetricSpace J]

omit [PseudoMetricSpace J] in
lemma normDistance_self (q : J → ℝ) : normDistance q q = 0 := by
  simp [normDistance]

omit [PseudoMetricSpace J] in
lemma normDistance_triangle (q r s : J → ℝ) :
    normDistance q s ≤ normDistance q r + normDistance r s := by
  simpa only [normDistance, dist_eq_norm] using dist_triangle q r s

end RadialLaws

end
end AlgorithmicThinTrees.MetricProfiles.CompactGeometry

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_AssignedGeometry
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric assigned geometry. -/

section

namespace AlgorithmicThinTrees.MetricProfiles.CompactGeometry
noncomputable section
open Finset
open StrongThinTree.Geometry (clamp )

variable {J : Type*} [Fintype J] [PseudoMetricSpace J]

omit [PseudoMetricSpace J] in
lemma normDistance_nonneg (x y : J → ℝ) : 0 ≤ normDistance x y := norm_nonneg _

end
end AlgorithmicThinTrees.MetricProfiles.CompactGeometry
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_BagExtraction
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric bag extraction. -/

section

namespace AlgorithmicThinTrees.MetricProfiles.CompactGeometry
noncomputable section
open Finset
open StrongThinTree.Geometry (retain_fibers)
open scoped Classical
variable {V I : Type*} [DecidableEq V] [DecidableEq I] {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord]

omit [DecidableEq V] in
lemma distance_balls_disjoint (X : V → Coord → ℝ) (u v : V) {r : ℝ}
    (hsep : 2*r ≤ normDistance (X u) (X v)) :
    Disjoint ((RadialShell.ball u r).support X) ((RadialShell.ball v r).support X) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  have hx := normDistance_triangle (X u) z (X v)
  rw [normDistance_comm (X u) z] at hx
  have hz₁ := hz.2.1
  have hz₂ := hz'.2.1
  change normDistance z (X u) < r at hz₁
  change normDistance z (X v) < r at hz₂
  linarith

omit [PseudoMetricSpace Coord] in
lemma separated_net (X : V → Coord → ℝ) (F : Finset V) (hF : F.Nonempty)
    {r : ℝ} (hr : 0 ≤ r) :
    ∃S : Finset V, S ⊆ F ∧ S.Nonempty ∧
      (∀u ∈ S, ∀v ∈ S, u ≠ v → r < normDistance (X u) (X v)) ∧
      ∀u ∈ F, ∃v ∈ S, normDistance (X u) (X v) ≤ r := by
  let sep : Finset V → Prop := fun S => ∀u ∈ S, ∀v ∈ S, u ≠ v → r < normDistance (X u) (X v)
  let good := F.powerset.filter sep
  have hgood : good.Nonempty := ⟨∅,mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),by simp [sep]⟩⟩
  obtain ⟨S,hS,hmax⟩ := exists_max_image good card hgood
  obtain ⟨hSF,hsep⟩ := mem_filter.mp hS
  have hcover : ∀u ∈ F, ∃v ∈ S, normDistance (X u) (X v) ≤ r := by
    intro u hu
    by_contra! hn
    have huS : u ∉ S := by
      intro huS
      have hh := hn u huS
      rw [normDistance_self] at hh
      linarith
    have hnew : insert u S ∈ good := by
      apply mem_filter.mpr
      refine ⟨mem_powerset.mpr (insert_subset hu (mem_powerset.mp hSF)),?_⟩
      intro x hx y hy hxy
      rcases mem_insert.mp hx with rfl | hxS
      · rcases mem_insert.mp hy with rfl | hyS
        · exact (hxy rfl).elim
        · exact hn y hyS
      · rcases mem_insert.mp hy with rfl | hyS
        · rw [normDistance_comm]; exact hn x hxS
        · exact hsep x hxS y hyS hxy
    have hh := hmax _ hnew
    rw [card_insert_of_notMem huS] at hh
    omega
  refine ⟨S,mem_powerset.mp hSF,?_,hsep,hcover⟩
  obtain ⟨u,hu⟩ := hF
  obtain ⟨v,hv,_⟩ := hcover u hu
  exact ⟨v,hv⟩

end
end AlgorithmicThinTrees.MetricProfiles.CompactGeometry

namespace AlgorithmicThinTrees.MetricProfiles.CompactGeometry
noncomputable section
open Finset
open StrongThinTree.Geometry (retain_fibers)
open RadialShell
open scoped Classical
variable {V : Type*} [DecidableEq V] {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {X : V → Coord → ℝ}

lemma compact_from_net (S W : Finset V) (hS : S.Nonempty) (hW : W.Nonempty)
    {δ D : ℝ} (hδ : 0 < δ) (hD : δ ≤ D)
    (hsep : (S : Set V).Pairwise (fun u v =>
      Disjoint ((ball u δ).support X) ((ball v δ).support X)))
    (hcover : ∀u ∈ S, ∃v ∈ W, normDistance (X u) (X v) ≤ 3*D)
    (hsmall : 432*D*(W.card : ℝ) ≤ δ*(S.card : ℝ)) :
    ∃F : CompactFamily X δ (6*D),
      δ*(S.card : ℝ)/2 ≤ δ*(∑B ∈ F.bags, (B.card : ℝ)) := by
  have hD0 : 0 < D := hδ.trans_le hD
  obtain ⟨w0,hw0⟩ := hW
  have hex : ∀u : V, ∃v ∈ W, u ∈ S → normDistance (X u) (X v) ≤ 3*D := by
    intro u
    by_cases hu : u ∈ S
    · obtain ⟨v,hv,hvu⟩ := hcover u hu
      exact ⟨v,hv,fun _ => hvu⟩
    · exact ⟨w0,hw0,fun hh => (hu hh).elim⟩
  choose f hfW hfDist using hex
  let fiber := fun i => S.filter (fun u => f u=i)
  let c : ℝ := 216*D/δ
  have hc : 0 < c := by dsimp [c] <;> positivity
  obtain ⟨J,hJW,hJ,hgain⟩ := retain_fibers S W f (fun u _ => hfW u)
    (fun _ => (1:ℝ)) (fun _ _ => zero_lt_one) hc
  have hsumRet : (∑i ∈ J, ((fiber i).card : ℝ)) ≥ (S.card : ℝ)/2 := by
    have hcost : c*(W.card : ℝ) ≤ (S.card : ℝ)/2 := by
      dsimp [c]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hδ).mpr
      nlinarith
    simp only [sum_const, nsmul_eq_mul,mul_one] at hgain
    dsimp [fiber]
    linarith
  have hJne : J.Nonempty := by
    by_contra hh
    rw [not_nonempty_iff_eq_empty.mp hh,sum_empty] at hsumRet
    have hs0 : (0:ℝ) < S.card := by exact_mod_cast card_pos.mpr hS
    linarith
  have hinj : Set.InjOn fiber J := by
    intro i hi j hj hij
    obtain ⟨u,hu⟩ := (hJ i hi).1
    have huj : u ∈ fiber j := hij ▸ hu
    exact (mem_filter.mp hu).2.symm.trans (mem_filter.mp huj).2
  have hfiber : ∀i ∈ J, fiber i ⊆ S := fun i _ => filter_subset _ _
  let F : CompactFamily X δ (6*D) := {
    bags := J.image fiber
    nonempty := hJne.image fiber
    radius_pos := hδ
    bags_disjoint := by
      intro A hA B hB hAB
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hA
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hB
      apply Finset.disjoint_left.mpr
      intro u hui huj
      have hij := (mem_filter.mp hui).2.symm.trans (mem_filter.mp huj).2
      exact hAB (congrArg fiber hij)
    balls_disjoint := by
      intro u hu v hv huv
      obtain ⟨A,hA,huA⟩ := mem_biUnion.mp hu
      obtain ⟨B,hB,hvB⟩ := mem_biUnion.mp hv
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hA
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hB
      exact hsep (hfiber i hi huA) (hfiber j hj hvB) huv
    cardinal := by
      intro A hA
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hA
      have hh := (hJ i hi).2
      have h216 : (216:ℝ) ≤ c := (le_div_iff₀ hδ).mpr (by nlinarith)
      have : (2:ℝ) ≤ (fiber i).card := by dsimp [fiber]; nlinarith
      exact_mod_cast this
    diameter := by
      intro A hA u hu v hv
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hA
      have hui := (mem_filter.mp hu).2
      have hvi := (mem_filter.mp hv).2
      have hu' := hfDist u (hfiber i hi hu)
      have hv' := hfDist v (hfiber i hi hv)
      rw [hui] at hu'
      rw [hvi,normDistance_comm (X v) (X i)] at hv'
      have htri := normDistance_triangle (X u) (X i) (X v)
      linarith
    compact := by
      intro A hA
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hA
      have hh := (hJ i hi).2
      rw [mul_one] at hh
      have hm := (div_le_iff₀ hδ).mp hh
      nlinarith }
  refine ⟨F,?_⟩
  have he : (∑B ∈ F.bags, (B.card : ℝ)) = ∑i ∈ J, ((fiber i).card : ℝ) :=
    sum_image hinj
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hsumRet hδ.le]

end
end AlgorithmicThinTrees.MetricProfiles.CompactGeometry

namespace AlgorithmicThinTrees.MetricProfiles.CompactGeometry
noncomputable section
open Finset
open StrongThinTree.Geometry (retain_fibers)
open RadialShell
open scoped Classical
variable {V I J : Type*} [DecidableEq V] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J] {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord]

lemma normalized_small_balls (X : V → Coord → ℝ) (Y : V → EuclideanSpace ℝ J)
    (u v : I → V) (j : I → J) (hj : Function.Injective j)
    (hN : 0 < Fintype.card I) {a ε c₁ : ℝ}
    (ha : 0 < a) (hε : 0 < ε) (hε1 : ε < 1/3) (hc : 0 < c₁)
    (hdiag : ∀i, 0 ≤ (Y (u i)-Y (v i)).ofLp (j i) ∧
      c₁ ≤ ((Y (u i)-Y (v i)).ofLp (j i))^2)
    (hbound : a * Fintype.card I * (∑i, ‖Y (u i)-Y (v i)‖^2) ≤
      (∑i, (Y (u i)-Y (v i)).ofLp (j i))^2)
    (hcontract : ∀x y, ‖Y x-Y y‖^2 ≤ normDistance (X x) (X y)) :
    a ≤ 1 ∧ ∃S : Finset V, ∃δ : ℝ, 0 < δ ∧
      S ⊆ (univ.image u ∪ univ.image v) ∧ 2 ≤ S.card ∧
      ε^2*a*Fintype.card I ≤ 1024*S.card ∧
      (S.card : ℝ)*δ = a^ε*c₁*Fintype.card I/(1024/ε^2) ∧
      (S : Set V).Pairwise (fun x y =>
        Disjoint ((ball x δ).support X) ((ball y δ).support X)) := by
  let N : ℝ := Fintype.card I
  let A : ℝ := ∑i, (Y (u i)-Y (v i)).ofLp (j i)
  have hN0 : 0 < N := by dsimp [N]; exact_mod_cast hN
  have hsqrt : ∀i, Real.sqrt c₁ ≤ (Y (u i)-Y (v i)).ofLp (j i) := by
    intro i
    exact (Real.sqrt_le_iff).mpr ⟨(hdiag i).1,(hdiag i).2⟩
  have hsum : N*Real.sqrt c₁ ≤ A := by
    simpa only [sum_const,nsmul_eq_mul,card_univ,N,A] using sum_le_sum (fun i (_ : i ∈ univ) => hsqrt i)
  have hA0 : 0 < A := (mul_pos hN0 (Real.sqrt_pos.mpr hc)).trans_le hsum
  have hA2 : c₁*N^2 ≤ A^2 := by
    have hh := sq_le_sq₀ (by positivity : 0 ≤ N*Real.sqrt c₁) hA0.le |>.mpr hsum
    rw [mul_pow,Real.sq_sqrt hc.le] at hh
    nlinarith
  obtain ⟨ha1,S,r,hr,hSF,hS2,hcard,hmass,hsep⟩ :=
    StrongThinTree.Spectral.spectral_packing_coordinates Y u v j hj ha hε hε1
      (by change 0 < A^2; positivity) hbound
  have hS0 : (0:ℝ) < S.card := by exact_mod_cast (by omega : 0 < S.card)
  have he2 : 0 < ε^2 := sq_pos_of_pos hε
  have hpow : 0 < a^ε := Real.rpow_pos_of_pos ha _
  let C : ℝ := 1024/ε^2
  have hC : 0 < C := by dsimp [C] <;> positivity
  let w := a^ε*c₁*N/C
  let δ := w/S.card
  have hw : 0 < w := by dsimp [w] <;> positivity
  have hδ : 0 < δ := div_pos hw hS0
  have hwle : w ≤ (S.card : ℝ)*r := by
    have hh := mul_le_mul_of_nonneg_left hA2 (show 0 ≤ ε^2*a^ε by positivity)
    change ε^2*a^ε*A^2 ≤ 1024*N*(S.card*r) at hmass
    have hh' : ε^2*a^ε*c₁*N ≤ 1024*(S.card*r) := by
      apply (mul_le_mul_iff_right₀ hN0).mp
      nlinarith
    dsimp [w,C]
    exact (div_le_iff₀ (div_pos (by norm_num) he2)).mpr (by
      rw [←mul_div_assoc]
      apply (le_div_iff₀ he2).mpr
      nlinarith)
  have hδr : δ ≤ r := (div_le_iff₀ hS0).mpr (by nlinarith)
  refine ⟨ha1,S,δ,hδ,hSF,hS2,hcard,?_,?_⟩
  · dsimp [δ,w,C,N]
    field_simp
  · intro x hx y hy hxy
    apply distance_balls_disjoint
    have hh := hsep x hx y hy hxy
    have hh' := hcontract x y
    have hs : (Real.sqrt r)^2 = r := Real.sq_sqrt hr.le
    have hnorm := norm_nonneg (Y x-Y y)
    have hroot := Real.sqrt_nonneg r
    nlinarith

end
end AlgorithmicThinTrees.MetricProfiles.CompactGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
open StrongThinTree.Geometry (retain_fibers)
open scoped Classical
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ}

lemma assigned_from_net (T : Finset (Finset (Fin n))) (W : Finset (Fin n))
    (hW : W.Nonempty) (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
    (hboundary : ∀t ∈ T, 0 < (parentBoundary H G t).card)
    {D η : ℝ} (hD : 0 < D)
    (hsep : (W : Set (Fin n)).Pairwise (fun u v =>
      Disjoint ((ball u D).support X) ((ball v D).support X)))
    (hcenter : ∀u ∈ W, ∃t ∈ T, u ∈ t ∧ ∃e ∈ parentBoundary H G t,
      (G.left e = u ∨ G.right e = u) ∧ normDistance (X (G.left e)) (X (G.right e)) < D)
    (hη : η ≤ (W.card : ℝ)/(2*(∑t ∈ T, ((parentBoundary H G t).card : ℝ)))) :
    ∃F : AssignedFamily H G X η, F.radius = D ∧ F.owners ⊆ T ∧
      D*(W.card : ℝ)/2 ≤ F.mass := by
  obtain ⟨u0,hu0⟩ := hW
  obtain ⟨t0,ht0,ht0c⟩ := hcenter u0 hu0
  have hex : ∀u : Fin n, ∃t ∈ T, u ∈ W → u ∈ t ∧ ∃e ∈ parentBoundary H G t,
      (G.left e = u ∨ G.right e = u) ∧ normDistance (X (G.left e)) (X (G.right e)) < D := by
    intro u
    by_cases hu : u ∈ W
    · obtain ⟨t,ht,hc⟩ := hcenter u hu
      exact ⟨t,ht,fun _ => hc⟩
    · exact ⟨t0,ht0,fun hh => (hu hh).elim⟩
  choose f hfT hf using hex
  let N : ℝ := ∑t ∈ T, ((parentBoundary H G t).card : ℝ)
  have hN : 0 < N := sum_pos (fun t ht => by exact_mod_cast hboundary t ht) ⟨t0,ht0⟩
  have hW0 : (0:ℝ) < W.card := by exact_mod_cast card_pos.mpr ⟨u0,hu0⟩
  let c : ℝ := W.card/(2*N)
  have hc : 0 < c := div_pos hW0 (mul_pos (by norm_num) hN)
  obtain ⟨J,hJT,hJ,hgain⟩ := retain_fibers W T f (fun u _ => hfT u)
    (fun t => ((parentBoundary H G t).card : ℝ))
    (fun t ht => by exact_mod_cast hboundary t ht) hc
  let fiber := fun t => W.filter (fun u => f u=t)
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let a (t : J) : AssignedBag H G X D η := {
    owner := t.val
    owner_mem := hT (hJT t.property)
    nonroot := hroot t.val (hJT t.property)
    centers := fiber t.val
    nonempty := (hJ t.val t.property).1
    radius_pos := hD
    disjoint := hsep.mono (filter_subset _ _)
    assignment := (mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg _)).trans (hJ t.val t.property).2
    endpoint := by
      intro u hu
      obtain ⟨hu,hfu⟩ := mem_filter.mp hu
      simpa only [hfu] using hf u hu }
  let F : AssignedFamily H G X η := {
    radius := D
    positive := hD
    count := Fintype.card J
    bag := fun i => a (e i)
    owner_injective := by
      intro i j hij
      exact e.injective (Subtype.ext hij)
    separated := by
      intro i u hu j v hv hne
      apply hsep (mem_filter.mp hu).1 (mem_filter.mp hv).1
      intro huv
      subst v
      have hh : (e i).val = (e j).val :=
        (mem_filter.mp hu).2.symm.trans (mem_filter.mp hv).2
      rcases hne with hne | hne
      · exact hne (e.injective (Subtype.ext hh))
      · exact hne rfl }
  have hsum : (∑i : Fin F.count, ((F.bag i).centers.card : ℝ)) =
      ∑t ∈ J, ((fiber t).card : ℝ) := by
    change (∑i : Fin (Fintype.card J), ((fiber (e i).val).card : ℝ)) = _
    rw [e.sum_comp (fun t : J => ((fiber t.val).card : ℝ))]
    exact sum_coe_sort J (fun t => ((fiber t).card : ℝ))
  refine ⟨F,rfl,?_,?_⟩
  · intro t ht
    obtain ⟨i,hi,rfl⟩ := mem_image.mp ht
    exact hJT (e i).property
  · have heq : c*N = (W.card : ℝ)/2 := by dsimp [c]; field_simp
    change (W.card : ℝ)-c*N ≤ _ at hgain
    rw [heq] at hgain
    change D*(W.card : ℝ)/2 ≤ (∑i : Fin F.count, ((F.bag i).centers.card : ℝ))*D
    rw [hsum]
    have hh := mul_le_mul_of_nonneg_left hgain hD.le
    nlinarith

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
open StrongThinTree.Geometry (retain_fibers)
open scoped Classical
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ}

lemma capture_small_balls (T : Finset (Finset (Fin n))) (S P : Finset (Fin n))
    (hS : S.Nonempty) (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
    (hboundary : ∀t ∈ T, 0 < (parentBoundary H G t).card)
    {δ c₂ η : ℝ} (hδ : 0 < δ) (hc : 0 < c₂) (_hη : 0 ≤ η)
    (hsep : (S : Set (Fin n)).Pairwise (fun u v =>
      Disjoint ((ball u δ).support X) ((ball v δ).support X)))
    (hcover : ∀u ∈ S, ∃v ∈ P, normDistance (X u) (X v) ≤ c₂)
    (hP : ∀u ∈ P, ∃t ∈ T, u ∈ t ∧ ∃e ∈ parentBoundary H G t,
      (G.left e = u ∨ G.right e = u) ∧ normDistance (X (G.left e)) (X (G.right e)) ≤ c₂)
    (hηδ : 864*η*(∑t ∈ T, ((parentBoundary H G t).card : ℝ)) ≤ S.card)
    (hηc : 1728*η*c₂*(∑t ∈ T, ((parentBoundary H G t).card : ℝ)) ≤ δ*S.card) :
    (∃F : CompactFamily X δ (6*max δ (2*c₂)),
      δ*(S.card : ℝ)/864 ≤ δ*(∑B ∈ F.bags, (B.card : ℝ))) ∨
    (∃F : AssignedFamily H G X η, F.radius = max δ (2*c₂) ∧ F.owners ⊆ T ∧
      δ*(S.card : ℝ)/864 ≤ F.mass) := by
  let D := max δ (2*c₂)
  have hD : 0 < D := hδ.trans_le (le_max_left _ _)
  have hcD : c₂ < D := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  obtain ⟨u0,hu0⟩ := hS
  obtain ⟨v0,hv0,hv0d⟩ := hcover u0 hu0
  have hPne : P.Nonempty := ⟨v0,hv0⟩
  obtain ⟨W,hWP,hW,hWsep,hWcover⟩ := separated_net X P hPne (show 0 ≤ 2*D by positivity)
  have hballs : (W : Set (Fin n)).Pairwise (fun u v =>
      Disjoint ((ball u D).support X) ((ball v D).support X)) := by
    intro u hu v hv huv
    exact distance_balls_disjoint X u v (hWsep u hu v hv huv).le
  have hcover' : ∀u ∈ S, ∃v ∈ W, normDistance (X u) (X v) ≤ 3*D := by
    intro u hu
    obtain ⟨p,hp,hup⟩ := hcover u hu
    obtain ⟨v,hv,hpv⟩ := hWcover p hp
    exact ⟨v,hv,(normDistance_triangle (X u) (X p) (X v)).trans (by linarith)⟩
  by_cases hsmall : 432*D*(W.card : ℝ) ≤ δ*(S.card : ℝ)
  · obtain ⟨F,hF⟩ := compact_from_net S W ⟨u0,hu0⟩ hW hδ (le_max_left _ _) hsep hcover' hsmall
    exact Or.inl ⟨F,(by nlinarith [show (0:ℝ) ≤ S.card from Nat.cast_nonneg _] : δ*(S.card : ℝ)/864 ≤ δ*(S.card : ℝ)/2).trans hF⟩
  · have hlarge : δ*(S.card : ℝ) < 432*D*(W.card : ℝ) := lt_of_not_ge hsmall
    have hcenter : ∀u ∈ W, ∃t ∈ T, u ∈ t ∧ ∃e ∈ parentBoundary H G t,
        (G.left e = u ∨ G.right e = u) ∧ normDistance (X (G.left e)) (X (G.right e)) < D := by
      intro u hu
      obtain ⟨t,ht,hut,e,he,heu,hlen⟩ := hP u (hWP hu)
      exact ⟨t,ht,hut,e,he,heu,hlen.trans_lt hcD⟩
    let N : ℝ := ∑t ∈ T, ((parentBoundary H G t).card : ℝ)
    obtain ⟨t0,ht0,ht0c⟩ := hP v0 hv0
    have hN : 0 < N := sum_pos (fun t ht => by exact_mod_cast hboundary t ht) ⟨t0,ht0⟩
    have hnumer : 864*η*N*D ≤ δ*(S.card : ℝ) := by
      rcases le_total δ (2*c₂) with hh | hh
      · dsimp [D]
        rw [max_eq_right hh]
        change 1728*η*c₂*N ≤ δ*(S.card : ℝ) at hηc
        nlinarith
      · dsimp [D]
        rw [max_eq_left hh]
        change 864*η*N ≤ (S.card : ℝ) at hηδ
        simpa [mul_comm δ] using mul_le_mul_of_nonneg_right hηδ hδ.le
    have hassign : η ≤ (W.card : ℝ)/(2*N) := by
      apply (le_div_iff₀ (mul_pos (by norm_num) hN)).mpr
      nlinarith
    obtain ⟨F,hFD,hFT,hgain⟩ := assigned_from_net T W hW hT hroot hboundary hD hballs hcenter hassign
    exact Or.inr ⟨F,hFD,hFT,(by nlinarith : δ*(S.card : ℝ)/864 ≤ D*(W.card : ℝ)/2).trans hgain⟩

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
open StrongThinTree.Geometry (retain_fibers)
open scoped Classical
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ}

lemma density_spectral_input {I : Type*} [Fintype I]
    (a d : I → ℝ) {c₁ c₂ α : ℝ}
    (hc₁ : 0 ≤ c₁) (hα : 0 ≤ α) (ha : ∀i, 0 ≤ a i)
    (hmin : ∀i, c₁ ≤ (a i)^2) (hd : ∀i, d i ≤ c₂)
    (hscale : α*c₂ ≤ c₁) :
    α*(Fintype.card I : ℝ)*(∑i, d i) ≤ (∑i, a i)^2 := by
  have hN : (0:ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  have hsum : (Fintype.card I : ℝ)*Real.sqrt c₁ ≤ ∑i, a i := by
    simpa only [sum_const,nsmul_eq_mul,card_univ] using
      sum_le_sum (fun i (_ : i ∈ univ) => Real.sqrt_le_iff.mpr ⟨ha i,hmin i⟩)
  have hsum0 : 0 ≤ ∑i, a i := sum_nonneg (fun i _ => ha i)
  have hsum2 : c₁*(Fintype.card I : ℝ)^2 ≤ (∑i, a i)^2 := by
    have hh := (sq_le_sq₀ (mul_nonneg hN (Real.sqrt_nonneg _)) hsum0).mpr hsum
    rw [mul_pow,Real.sq_sqrt hc₁] at hh
    nlinarith only [hh]
  have hdsum : (∑i, d i) ≤ (Fintype.card I : ℝ)*c₂ := by
    simpa only [sum_const,nsmul_eq_mul,card_univ] using sum_le_sum (fun i (_ : i ∈ univ) => hd i)
  have h1 := mul_le_mul_of_nonneg_left hdsum (mul_nonneg hα hN)
  have h2 := mul_le_mul_of_nonneg_right hscale (sq_nonneg (Fintype.card I : ℝ))
  nlinarith only [h1,h2,hsum2]

lemma homogeneous_family (T : Finset (Finset (Fin n))) (F : Finset (Fin n) → Finset (Fin m))
    (Y : Fin n → EuclideanSpace ℝ (Fin m))
    (hTne : T.Nonempty) (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
    (hF : ∀t ∈ T, F t ⊆ parentBoundary H G t) (hFn : ∀t ∈ T, (F t).Nonempty)
    {α γ ε c₁ c₂ : ℝ} (hα : 0 < α) (hγ : 0 < γ)
    (he : 0 < ε) (he1 : ε < 1/3) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hcontract : ∀u v, ‖Y u-Y v‖^2 ≤ normDistance (X u) (X v))
    (hpositive : ∀e, 0 ≤ (Y (G.left e)-Y (G.right e)).ofLp e)
    (hmin : ∀t ∈ T, ∀e ∈ F t, c₁ ≤ ((Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hmax : ∀t ∈ T, ∀e ∈ F t, ((Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤ 4*c₁)
    (hdmin : ∀t ∈ T, ∀e ∈ F t, c₂/4 ≤ normDistance (X (G.left e)) (X (G.right e)))
    (hdmax : ∀t ∈ T, ∀e ∈ F t, normDistance (X (G.left e)) (X (G.right e)) ≤ c₂)
    (hbad : ∀t ∈ T, α*((parentBoundary H G t).card : ℝ)*
      (∑e ∈ parentBoundary H G t, normDistance (X (G.left e)) (X (G.right e))) ≤
      (∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hdom : ∀t ∈ T, γ*(∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤
      (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hsmall : (α*γ/32)^ε ≤ 1/(1728*(1024/ε^2))) :
    let s := α*γ/32
    let R := ∑t ∈ T, (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/
      ((parentBoundary H G t).card : ℝ)
    (∃δ Δ : ℝ, ∃B : CompactFamily X δ Δ,
      s*c₁ ≤ δ ∧ Δ ≤ 12*c₁/s ∧ s^ε*R/(6912*(1024/ε^2)) ≤ δ*(∑D ∈ B.bags, (D.card : ℝ))) ∨
    (∃B : AssignedFamily H G X (s^(1+2*ε)), B.owners ⊆ T ∧
      s*c₁ ≤ B.radius ∧ B.radius ≤ 12*c₁/s ∧ s^ε*R/(6912*(1024/ε^2)) ≤ B.mass) := by
  let a : Fin m → ℝ := fun e => (Y (G.left e)-Y (G.right e)).ofLp e
  let d : Fin m → ℝ := fun e => normDistance (X (G.left e)) (X (G.right e))
  let E := T.biUnion F
  let N : ℝ := ∑t ∈ T, ((parentBoundary H G t).card : ℝ)
  let N' : ℝ := E.card
  let s := α*γ/32
  let C : ℝ := 1024/ε^2
  let R := ∑t ∈ T, (∑e ∈ F t, a e)^2/((parentBoundary H G t).card : ℝ)
  have hs : 0 < s := by dsimp [s] <;> positivity
  have hC : 0 < C := by dsimp [C] <;> positivity
  have hEn : E.Nonempty := by
    obtain ⟨t,ht⟩ := hTne
    obtain ⟨e,he⟩ := hFn t ht
    exact ⟨e,mem_biUnion.mpr ⟨t,ht,he⟩⟩
  have hN' : 0 < N' := by dsimp [N']; exact_mod_cast card_pos.mpr hEn
  have hboundary : ∀t ∈ T, 0 < (parentBoundary H G t).card :=
    fun t ht => card_pos.mpr ((hFn t ht).mono (hF t ht))
  have hN : 0 < N := by
    apply sum_pos (fun t ht => ?_) hTne
    exact_mod_cast hboundary t ht
  have hNle : N' ≤ N := by
    have h1 : E.card ≤ ∑t ∈ T, (F t).card := card_biUnion_le
    have h2 : (∑t ∈ T, (F t).card) ≤ ∑t ∈ T, (parentBoundary H G t).card :=
      sum_le_sum (fun t ht => card_le_card (hF t ht))
    dsimp [N',N]
    exact_mod_cast h1.trans h2
  have hd0 : ∀e, 0 ≤ d e := fun e => normDistance_nonneg _ _
  obtain ⟨hdensity,hR⟩ := StrongThinTree.BagDensity.family_density T (parentBoundary H G) F a d
    hα hγ hc₁.le hF hFn (fun t ht e he => hd0 e) hmax hdmin hbad hdom
    (H.subset_boundary_multiplicity G T hT hroot F hF)
  change s*N*c₂ ≤ c₁*N' at hdensity
  change R ≤ 8*c₁*N' at hR
  let specα := s*N/N'
  have ha0 : 0 < specα := div_pos (mul_pos hs hN) hN'
  have hscale : specα*N' = s*N := div_mul_cancel₀ _ hN'.ne'
  have has : s ≤ specα := by
    apply (le_div_iff₀ hN').mpr
    exact mul_le_mul_of_nonneg_left hNle hs.le
  have had : specα*c₂ ≤ c₁ := by
    change (s*N/N')*c₂ ≤ c₁
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hN').mpr hdensity
  have hminE : ∀e ∈ E, c₁ ≤ (a e)^2 := by
    intro e he
    obtain ⟨t,ht,he⟩ := mem_biUnion.mp he
    exact hmin t ht e he
  have hmaxE : ∀e ∈ E, d e ≤ c₂ := by
    intro e he
    obtain ⟨t,ht,he⟩ := mem_biUnion.mp he
    exact hdmax t ht e he
  let u : E → Fin n := fun e => G.left e.val
  let v : E → Fin n := fun e => G.right e.val
  have hIE : Fintype.card E = E.card := Fintype.card_coe E
  have hI : 0 < Fintype.card E := by rw [hIE]; exact card_pos.mpr hEn
  have hbnd : specα*(Fintype.card E : ℝ)*(∑e : E, ‖Y (u e)-Y (v e)‖^2) ≤
      (∑e : E, (Y (u e)-Y (v e)).ofLp e.val)^2 :=
    density_spectral_input (fun e : E => a e.val) (fun e : E => ‖Y (u e)-Y (v e)‖^2)
      hc₁.le ha0.le (fun e => hpositive e.val) (fun e => hminE e.val e.property)
      (fun e => (hcontract (u e) (v e)).trans (hmaxE e.val e.property)) had
  obtain ⟨ha1,S,δ,hδ,hSE,hS2,hSc,hmass,hsep⟩ := normalized_small_balls X Y u v
    (fun e : E => e.val) Subtype.val_injective hI ha0 he he1 hc₁
    (fun e => ⟨hpositive e.val,hminE e.val e.property⟩) hbnd hcontract
  have hS : S.Nonempty := card_pos.mp (by omega)
  have hSc0 : (0:ℝ) < S.card := by exact_mod_cast (by omega : 0 < S.card)
  have hcard : specα*N'/C ≤ (S.card : ℝ) := by
    apply (div_le_iff₀ hC).mpr
    dsimp [C]
    rw [←mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos he)).mpr
    rw [hIE] at hSc
    change ε^2*specα*N' ≤ _ at hSc
    nlinarith only [hSc]
  have hcard₂ : (S.card : ℝ) ≤ 2*N' := by
    have hh := card_le_card hSE
    have h1 := card_union_le (univ.image u) (univ.image v)
    have h2 := card_image_le (f := u) (s := univ)
    have h3 := card_image_le (f := v) (s := univ)
    simp only [card_univ,hIE] at h2 h3
    have hSc : S.card ≤ 2*E.card := by omega
    dsimp [N']; exact_mod_cast hSc
  rw [hIE] at hmass
  change (S.card : ℝ)*δ = specα^ε*c₁*N'/C at hmass
  obtain ⟨hηδ,hηc,hlower,hupper,hgain⟩ := StrongThinTree.CaptureNumeric.thresholds
    hs has ha1 he (by linarith : ε ≤ 1/2) hC hN hN' hNle hc₁ hc₂ hSc0 hδ
    hscale hdensity hcard hcard₂ hmass hsmall hR
  let P := T.biUnion (fun t => t.filter (fun w => ∃e ∈ F t, G.left e=w ∨ G.right e=w))
  have hP : ∀w ∈ P, ∃t ∈ T, w ∈ t ∧ ∃e ∈ parentBoundary H G t,
      (G.left e=w ∨ G.right e=w) ∧ normDistance (X (G.left e)) (X (G.right e)) ≤ c₂ := by
    intro w hw
    obtain ⟨t,ht,hw⟩ := mem_biUnion.mp hw
    obtain ⟨hwt,e,he,hew⟩ := mem_filter.mp hw
    exact ⟨t,ht,hwt,e,hF t ht he,hew,hdmax t ht e he⟩
  have hEnd : ∀e ∈ E, ∃w ∈ P, (G.left e=w ∨ G.right e=w) := by
    intro e he
    obtain ⟨t,ht,het⟩ := mem_biUnion.mp he
    have hc := (mem_filter.mp (hF t ht het)).2
    rcases hc with hc | hc
    · exact ⟨G.left e,mem_biUnion.mpr ⟨t,ht,mem_filter.mpr ⟨hc.1,e,het,Or.inl rfl⟩⟩,Or.inl rfl⟩
    · exact ⟨G.right e,mem_biUnion.mpr ⟨t,ht,mem_filter.mpr ⟨hc.1,e,het,Or.inr rfl⟩⟩,Or.inr rfl⟩
  have hcover : ∀w ∈ S, ∃p ∈ P, normDistance (X w) (X p) ≤ c₂ := by
    intro w hw
    rcases mem_union.mp (hSE hw) with hw | hw
    · obtain ⟨e,he,rfl⟩ := mem_image.mp hw
      obtain ⟨p,hp,hp'⟩ := hEnd e.val e.property
      refine ⟨p,hp,?_⟩
      rcases hp' with hp' | hp'
      · simpa [u,hp',normDistance_self] using hc₂.le
      · simpa [u,d,hp'] using hmaxE e.val e.property
    · obtain ⟨e,he,rfl⟩ := mem_image.mp hw
      obtain ⟨p,hp,hp'⟩ := hEnd e.val e.property
      refine ⟨p,hp,?_⟩
      rcases hp' with hp' | hp'
      · simpa [v,d,hp',normDistance_comm] using hmaxE e.val e.property
      · simpa [v,hp',normDistance_self] using hc₂.le
  have hNcast : ∑t ∈ T, ((parentBoundary H G t).card : ℝ) = N := rfl
  have hη : 0 ≤ s^(1+2*ε) := (Real.rpow_pos_of_pos hs _).le
  obtain hcomp | hass := capture_small_balls T S P hS hT hroot hboundary hδ hc₂ hη
    hsep hcover hP hηδ hηc
  · obtain ⟨B,hB⟩ := hcomp
    refine Or.inl ⟨δ,6*max δ (2*c₂),B,hlower,?_,hgain.trans hB⟩
    change 6*max δ (2*c₂) ≤ 12*c₁/s
    calc
      _ ≤ 6*(2*c₁/s) := mul_le_mul_of_nonneg_left hupper (by norm_num)
      _ = 12*c₁/s := by ring
  · obtain ⟨B,hBD,hBT,hB⟩ := hass
    refine Or.inr ⟨B,hBT,?_,?_,hgain.trans hB⟩
    · rw [hBD]
      exact hlower.trans (le_max_left _ _)
    · rw [hBD]
      have hh : 0 ≤ c₁/s := by positivity
      calc
        max δ (2*c₂) ≤ 2*c₁/s := hupper
        _ ≤ 12*c₁/s := by rw [mul_div_assoc,mul_div_assoc]; linarith only [hh]

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_ScaleCharging
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric scale charging. -/

section

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
open scoped Classical
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ}

lemma capturePackage_oai (T : Finset (Finset (Fin n))) (F : Finset (Fin n) → Finset (Fin m))
    (Y : Fin n → EuclideanSpace ℝ (Fin m))
    (hTne : T.Nonempty) (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
    (hF : ∀t ∈ T, F t ⊆ parentBoundary H G t) (hFn : ∀t ∈ T, (F t).Nonempty)
    {α γ ε c₁ c₂ : ℝ} (hα : 0 < α) (hγ : 0 < γ)
    (he : 0 < ε) (he1 : ε < 1/3) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hcontract : ∀u v, ‖Y u-Y v‖^2 ≤ normDistance (X u) (X v))
    (hpositive : ∀e, 0 ≤ (Y (G.left e)-Y (G.right e)).ofLp e)
    (hmin : ∀t ∈ T, ∀e ∈ F t, c₁ ≤ ((Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hmax : ∀t ∈ T, ∀e ∈ F t, ((Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤ 4*c₁)
    (hdmin : ∀t ∈ T, ∀e ∈ F t, c₂/4 ≤ normDistance (X (G.left e)) (X (G.right e)))
    (hdmax : ∀t ∈ T, ∀e ∈ F t, normDistance (X (G.left e)) (X (G.right e)) ≤ c₂)
    (hbad : ∀t ∈ T, α*((parentBoundary H G t).card : ℝ)*
      (∑e ∈ parentBoundary H G t, normDistance (X (G.left e)) (X (G.right e))) ≤
      (∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hdom : ∀t ∈ T, γ*(∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤
      (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hsmall : (α*γ/32)^ε ≤ 1/(1728*(1024/ε^2)))
    {q : ℕ} {ρ : ℝ}
    (hassign : (6144:ℝ)/q ≤ (α*γ/32)^(1+2*ε))
    (hratio : ∀t ∈ T, (q:ℝ)*ρ*((G.cut univ t).card : ℝ) ≤ (parentBoundary H G t).card) :
    let s := α*γ/32
    let R := ∑t ∈ T, (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/
      ((parentBoundary H G t).card : ℝ)
    ∃B : CapturedFamily H G X (6144/q), B.owners ⊆ T ∧ B.Ratio ρ ∧
      s*c₁ ≤ B.radius ∧ B.upper ≤ 12*c₁/s ∧ s^ε*R/(6912*(1024/ε^2)) ≤ B.mass := by
  obtain hC | hA := homogeneous_family T F Y hTne hT hroot hF hFn hα hγ he he1 hc₁ hc₂
    hcontract hpositive hmin hmax hdmin hdmax hbad hdom hsmall
  · obtain ⟨δ,Δ,B,hl,hu,hg⟩ := hC
    exact ⟨.inl ⟨δ,Δ,B⟩,empty_subset _,trivial,hl,hu,hg⟩
  · obtain ⟨B,hBT,hl,hu,hg⟩ := hA
    refine ⟨.inr (B.weaken hassign),hBT,?_,hl,hu,hg⟩
    intro i
    apply hratio
    apply hBT
    exact mem_image.mpr ⟨i,mem_univ _,rfl⟩

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.capturePackage_oai.{u_1} := @OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.capturePackage_oai.{u_1}
