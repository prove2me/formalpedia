-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_inv_mul_gauge3_le_norm_vecMul_of_forall_mem_adicCompletionIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/25bfcc75-25d2-5624-9295-bd3a9a51b5e7

import Definitions.Def_LanglandsTunnell_CubicInduction_Growth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_inv_mul_gauge3_le_norm_vecMul_of_forall_mem_adicCompletionIntegers

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain LanglandsTunnell.CubicInduction
open scoped NNReal

namespace KcFirstMin

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "𝔸f" => IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ

def re : 𝔸 →+* ℝ :=
  ((InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).comp
    (Pi.evalRingHom (fun v : InfinitePlace ℚ => v.Completion) Rat.infinitePlace)).comp
    (RingHom.fst (InfiniteAdeleRing ℚ) 𝔸f)

theorem re_apply (x : 𝔸) :
    re x = InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (x.1 Rat.infinitePlace) :=
  rfl

theorem abs_re (x : 𝔸) : |re x| = ‖x.1 Rat.infinitePlace‖ := by
  rw [re_apply, ← Real.norm_eq_abs]
  exact Isometry.norm_map_of_map_zero
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace) (map_zero _) _

theorem re_algebraMap (q : ℚ) : re (algebraMap ℚ 𝔸 q) = q :=
  eq_ratCast (re.comp (algebraMap ℚ 𝔸)) q

section Finite

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem norm_le_one_iff_mem (x : v.adicCompletion ℚ) : ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, FinitePlace.norm_def, ← NNReal.coe_one, NNReal.coe_le_coe,
    WithZeroMulInt.toNNReal_le_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal v)]

theorem norm_eq_one_of_valued_eq_one {x : v.adicCompletion ℚ} (hx : Valued.v x = 1) : ‖x‖ = 1 := by
  rw [FinitePlace.norm_def, hx, map_one, NNReal.coe_one]

variable {v}

theorem nnnorm_inv_apply_le_matrixSupSize (k : GL (Fin 3) (v.adicCompletion ℚ)) (i j : Fin 3) :
    ‖((k⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j‖₊ ≤
      matrixSupSize k := by
  unfold matrixSupSize
  exact Finset.le_sup_of_le (Finset.mem_univ (i, j)) (le_max_right _ _)

theorem nnnorm_apply_le_matrixSupSize (k : GL (Fin 3) (v.adicCompletion ℚ)) (i j : Fin 3) :
    ‖(k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j‖₊ ≤ matrixSupSize k := by
  unfold matrixSupSize
  exact Finset.le_sup_of_le (Finset.mem_univ (i, j)) (le_max_left _ _)

theorem matrixSupSize_eq_one_of_integral (k : GL (Fin 3) (v.adicCompletion ℚ))
    (hk : ∀ i j, (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ)
    (hk' : ∀ i j, ((k⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j ∈
      v.adicCompletionIntegers ℚ) :
    matrixSupSize k = 1 := by
  apply le_antisymm
  · unfold matrixSupSize
    refine Finset.sup_le fun ij _ => max_le ?_ ?_
    · rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
      exact (norm_le_one_iff_mem v _).mpr (hk ij.1 ij.2)
    · rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
      exact (norm_le_one_iff_mem v _).mpr (hk' ij.1 ij.2)
  ·
    have h1 : ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
        ((k⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) 0 0 = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [Matrix.mul_apply] at h1
    by_contra hlt
    rw [not_le] at hlt
    have hterm : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
        Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 j *
          ((k⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) j 0) < 1 := by
      intro j _
      rw [map_mul]
      have ha : Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 j) ≤ 1 :=
        (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hk 0 j)
      have hb : Valued.v (((k⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) :
          Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) j 0) < 1 := by
        by_contra hge
        rw [not_lt] at hge
        have heq : Valued.v (((k⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) :
            Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) j 0) = 1 :=
          le_antisymm ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hk' j 0)) hge
        have hone : ‖((k⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) j 0‖₊
            = 1 := by
          rw [← NNReal.coe_inj, coe_nnnorm, NNReal.coe_one]
          exact norm_eq_one_of_valued_eq_one v heq
        exact (lt_irrefl _) (hlt.trans_le (hone ▸ nnnorm_inv_apply_le_matrixSupSize k j 0))
      calc Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 j) *
            Valued.v (((k⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) j 0)
          ≤ 1 * Valued.v (((k⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) :
              Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) j 0) := mul_le_mul_left ha _
        _ < 1 := by rw [one_mul]; exact hb
    have hsum := Valued.v.map_sum_lt (one_ne_zero : (1 : WithZero (Multiplicative ℤ)) ≠ 0) hterm
    rw [h1, map_one] at hsum
    exact lt_irrefl _ hsum

end Finite

section Global

variable (g : AdelicGL 3 (𝓞 ℚ) ℚ)

theorem componentAt3_coe_apply (w : HeightOneSpectrum (𝓞 ℚ)) (i j : Fin 3) :
    ((componentAt3 (𝓞 ℚ) ℚ w g : GL (Fin 3) (w.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ)) i j =
      ((g : Matrix (Fin 3) (Fin 3) 𝔸) i j).2 w := rfl

theorem componentAt3_inv_coe_apply (w : HeightOneSpectrum (𝓞 ℚ)) (i j : Fin 3) :
    (((componentAt3 (𝓞 ℚ) ℚ w g)⁻¹ : GL (Fin 3) (w.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ)) i j =
      (((g⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) i j).2 w := by
  rw [← map_inv]
  rfl

theorem finite_setOf_not_mem_integers (x : 𝔸f) :
    {w : HeightOneSpectrum (𝓞 ℚ) | x w ∉ w.adicCompletionIntegers ℚ}.Finite :=
  Filter.eventually_cofinite.1 x.2

def localSize (w : HeightOneSpectrum (𝓞 ℚ)) : ℝ := ((matrixSupSize (componentAt3 (𝓞 ℚ) ℚ w g) : ℝ≥0) : ℝ)

theorem finGauge3_eq : finGauge3 ℚ g = ∏ᶠ w, localSize g w := rfl

theorem hasFiniteMulSupport_localSize : (localSize g).HasFiniteMulSupport := by
  refine Set.Finite.subset (Set.finite_iUnion fun i : Fin 3 => Set.finite_iUnion fun j : Fin 3 =>
    (finite_setOf_not_mem_integers ((g : Matrix (Fin 3) (Fin 3) 𝔸) i j).2).union
      (finite_setOf_not_mem_integers (((g⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) i j).2)) ?_
  intro w hw
  by_contra hmem
  simp only [Set.mem_iUnion, Set.mem_union, Set.mem_setOf_eq, not_exists, not_or, not_not] at hmem
  refine hw ?_
  change ((matrixSupSize (componentAt3 (𝓞 ℚ) ℚ w g) : ℝ≥0) : ℝ) = 1
  rw [matrixSupSize_eq_one_of_integral _ (fun i j => ?_) (fun i j => ?_), NNReal.coe_one]
  · rw [componentAt3_coe_apply]
    exact (hmem i j).1
  · rw [componentAt3_inv_coe_apply]
    exact (hmem i j).2

theorem localSize_nonneg (w : HeightOneSpectrum (𝓞 ℚ)) : 0 ≤ localSize g w := NNReal.coe_nonneg _

theorem finGauge3_nonneg : 0 ≤ finGauge3 ℚ g := finprod_nonneg fun w => localSize_nonneg g w

end Global

section Bound

variable (g : AdelicGL 3 (𝓞 ℚ) ℚ) (ξ : Fin 3 → ℚ)

def diag : Fin 3 → 𝔸 := fun i => algebraMap ℚ 𝔸 (ξ i)

def eta : Fin 3 → 𝔸 := Matrix.vecMul (diag ξ) (g : Matrix (Fin 3) (Fin 3) 𝔸)

theorem diag_eq_vecMul_eta : diag ξ = Matrix.vecMul (eta g ξ) ((g⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) := by
  unfold eta
  rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

theorem diag_apply_eq_sum (i : Fin 3) :
    diag ξ i = ∑ j, eta g ξ j * (((g⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) j i) := by
  conv_lhs => rw [diag_eq_vecMul_eta g ξ]
  rfl

theorem abs_le_mul_archGauge3 (i : Fin 3) {m : ℝ} (hm0 : 0 ≤ m) (hm : ∀ j, |re (eta g ξ j)| ≤ m) :
    |(ξ i : ℝ)| ≤ m * archGauge3 ℚ g := by
  have hre : (ξ i : ℝ) = ∑ j, re (eta g ξ j) * re (((g⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) j i) := by
    rw [← re_algebraMap (ξ i)]
    change re (diag ξ i) = _
    rw [diag_apply_eq_sum g ξ i, map_sum]
    simp only [map_mul]

  set k : GL (Fin 3) (Rat.infinitePlace.Completion) := archPlaceComponent3 ℚ Rat.infinitePlace g with hk
  have hcol : ∀ j, |re (((g⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) j i)| =
      ‖((k⁻¹ : GL (Fin 3) Rat.infinitePlace.Completion) : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) j i‖ := by
    intro j
    rw [abs_re, hk, ← map_inv]
    rfl
  have hsize : ∑ j, ‖((k⁻¹ : GL (Fin 3) Rat.infinitePlace.Completion) :
      Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) j i‖ ≤ matrixSize k := by
    unfold matrixSize
    refine Finset.sum_le_sum fun j _ => ?_
    set K : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion :=
      ((k : GL (Fin 3) Rat.infinitePlace.Completion) : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion)
    set Ki : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion :=
      ((k⁻¹ : GL (Fin 3) Rat.infinitePlace.Completion) : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion)
    have h1 : ‖Ki j i‖ ≤ ‖K j i‖ + ‖Ki j i‖ := le_add_of_nonneg_left (norm_nonneg _)
    have h2 : ‖K j i‖ + ‖Ki j i‖ ≤ ∑ l, (‖K j l‖ + ‖Ki j l‖) :=
      Finset.single_le_sum (f := fun l => ‖K j l‖ + ‖Ki j l‖)
        (fun l _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ i)
    exact h1.trans h2
  have harch : matrixSize k ≤ archGauge3 ℚ g := by
    unfold archGauge3
    rw [Fintype.sum_unique, hk, Subsingleton.elim (default : InfinitePlace ℚ) Rat.infinitePlace]
    linarith [matrixSize_nonneg (archPlaceComponent3 ℚ Rat.infinitePlace g)]
  calc |(ξ i : ℝ)| = |∑ j, re (eta g ξ j) * re (((g⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) j i)| := by
        rw [hre]
    _ ≤ ∑ j, |re (eta g ξ j) * re (((g⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) j i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, m * ‖((k⁻¹ : GL (Fin 3) Rat.infinitePlace.Completion) :
          Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) j i‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, hcol]
        exact mul_le_mul_of_nonneg_right (hm j) (norm_nonneg _)
    _ = m * ∑ j, ‖((k⁻¹ : GL (Fin 3) Rat.infinitePlace.Completion) :
          Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) j i‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ m * archGauge3 ℚ g := mul_le_mul_of_nonneg_left (hsize.trans harch) hm0

def evalAt (w : HeightOneSpectrum (𝓞 ℚ)) : 𝔸 →+* w.adicCompletion ℚ :=
  (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)

theorem evalAt_apply (w : HeightOneSpectrum (𝓞 ℚ)) (x : 𝔸) : evalAt w x = x.2 w := rfl

theorem natCast_mul_apply (N : ℕ) (y : 𝔸f) (w : HeightOneSpectrum (𝓞 ℚ)) :
    ((N : 𝔸f) * y) w = (N : w.adicCompletion ℚ) * y w := by
  have h := map_mul (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w) (N : 𝔸f) y
  rw [map_natCast] at h
  exact h

theorem norm_algebraMap_le_localSize (N : ℕ) (i : Fin 3) (w : HeightOneSpectrum (𝓞 ℚ))
    (hint : ∀ j, ((N : 𝔸f) * (eta g ξ j).2) w ∈ w.adicCompletionIntegers ℚ) :
    ‖(algebraMap ℚ 𝔸f ((N : ℚ) * ξ i)) w‖ ≤ localSize g w := by
  have hsum : (algebraMap ℚ 𝔸f ((N : ℚ) * ξ i)) w =
      ∑ j, ((N : w.adicCompletion ℚ) * evalAt w (eta g ξ j)) *
        evalAt w ((((g⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) j i)) := by
    have h := congrArg (evalAt w) (diag_apply_eq_sum g ξ i)
    rw [map_sum] at h
    change (evalAt w) (algebraMap ℚ 𝔸 ((N : ℚ) * ξ i)) = _
    rw [map_mul, map_natCast, map_mul, map_natCast]
    change (N : w.adicCompletion ℚ) * evalAt w (diag ξ i) = _
    rw [h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, mul_assoc]
  rw [hsum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (localSize_nonneg g w) fun j _ => ?_
  rw [norm_mul]
  have ha : ‖(N : w.adicCompletion ℚ) * evalAt w (eta g ξ j)‖ ≤ 1 := by
    rw [evalAt_apply, ← natCast_mul_apply]
    exact (norm_le_one_iff_mem w _).mpr (hint j)
  have hb : ‖evalAt w ((((g⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) j i))‖ ≤ localSize g w := by
    have h := nnnorm_inv_apply_le_matrixSupSize (componentAt3 (𝓞 ℚ) ℚ w g) j i
    rw [componentAt3_inv_coe_apply] at h
    rw [evalAt_apply]
    exact_mod_cast h
  calc _ ≤ 1 * localSize g w := mul_le_mul ha hb (norm_nonneg _) zero_le_one
    _ = localSize g w := one_mul _

theorem one_le_mul_abs_mul_finGauge3 (N : ℕ) (i : Fin 3) (hξi : ξ i ≠ 0) (hN : 0 < N)
    (hint : ∀ j w, ((N : 𝔸f) * (eta g ξ j).2) w ∈ w.adicCompletionIntegers ℚ) :
    1 ≤ (N : ℝ) * |(ξ i : ℝ)| * finGauge3 ℚ g := by
  set x : ℚ := (N : ℚ) * ξ i with hx
  have hx0 : x ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr hN.ne') hξi
  have hpf := NumberField.prod_abs_eq_one hx0

  have hinf : (∏ w : InfinitePlace ℚ, w x ^ w.mult) = |(x : ℝ)| := by
    rw [Fintype.prod_unique]
    have hw : (default : InfinitePlace ℚ).IsReal := by
      rw [Subsingleton.elim (default : InfinitePlace ℚ) Rat.infinitePlace]
      exact Rat.isReal_infinitePlace
    rw [InfinitePlace.mult_isReal ⟨default, hw⟩, pow_one, Rat.infinitePlace_apply, Rat.cast_abs]

  have hfin : ∏ᶠ w : FinitePlace ℚ, w x ≤ finGauge3 ℚ g := by
    rw [finprod_eq_of_bijective (f := fun w : FinitePlace ℚ => w x)
      (g := fun w : HeightOneSpectrum (𝓞 ℚ) => FinitePlace.mk w x) FinitePlace.maximalIdeal
      FinitePlace.equivHeightOneSpectrum.bijective (fun w => by
        change w x = FinitePlace.mk (FinitePlace.maximalIdeal w) x
        rw [FinitePlace.mk_maximalIdeal]),
      finGauge3_eq]
    have hsupp : (fun w : HeightOneSpectrum (𝓞 ℚ) => FinitePlace.mk w x).HasFiniteMulSupport := by
      refine Set.Finite.subset ((FinitePlace.hasFiniteMulSupport hx0).image FinitePlace.maximalIdeal) ?_
      intro w hw
      refine ⟨FinitePlace.mk w, ?_, FinitePlace.maximalIdeal_mk w⟩
      exact hw
    refine finprod_le_finprod hsupp (fun w => apply_nonneg _ _) (hasFiniteMulSupport_localSize g) fun w => ?_
    change FinitePlace.mk w x ≤ localSize g w
    rw [FinitePlace.mk_apply]
    have h := norm_algebraMap_le_localSize g ξ N i w (fun j => hint j w)
    rw [FiniteAdeleRing.algebraMap_apply] at h
    exact h
  have hfin0 : 0 ≤ ∏ᶠ w : FinitePlace ℚ, w x := finprod_nonneg fun w => apply_nonneg _ _
  calc (1 : ℝ) = (∏ w : InfinitePlace ℚ, w x ^ w.mult) * ∏ᶠ w : FinitePlace ℚ, w x := hpf.symm
    _ ≤ |(x : ℝ)| * finGauge3 ℚ g := by
        rw [hinf]
        exact mul_le_mul_of_nonneg_left hfin (abs_nonneg _)
    _ = (N : ℝ) * |(ξ i : ℝ)| * finGauge3 ℚ g := by
        rw [hx, Rat.cast_mul, Rat.cast_natCast, abs_mul, Nat.abs_cast]

theorem exists_le_norm (N : ℕ) (hN : 0 < N) (hξ : ξ ≠ 0)
    (hint : ∀ j w, ((N : 𝔸f) * (eta g ξ j).2) w ∈ w.adicCompletionIntegers ℚ) :
    ∃ j, ((N : ℝ) * gauge3 ℚ g)⁻¹ ≤ ‖(eta g ξ j).1 Rat.infinitePlace‖ := by
  obtain ⟨i, hξi⟩ := Function.ne_iff.mp hξ
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image Finset.univ (fun j => |re (eta g ξ j)|) Finset.univ_nonempty
  refine ⟨j₀, ?_⟩
  rw [← abs_re]
  set m : ℝ := |re (eta g ξ j₀)| with hm
  have hm0 : 0 ≤ m := abs_nonneg _
  have harch := abs_le_mul_archGauge3 g ξ i hm0 fun j => hj₀ j (Finset.mem_univ j)
  have hpf := one_le_mul_abs_mul_finGauge3 g ξ N i hξi hN hint
  have hG1 : (1 : ℝ) ≤ gauge3 ℚ g := one_le_gauge3 ℚ g
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hprod : archGauge3 ℚ g * finGauge3 ℚ g ≤ gauge3 ℚ g := le_max_right _ _
  have hfin0 : 0 ≤ finGauge3 ℚ g := finGauge3_nonneg g

  have hkey : 1 ≤ (N : ℝ) * m * gauge3 ℚ g :=
    calc (1 : ℝ) ≤ (N : ℝ) * |(ξ i : ℝ)| * finGauge3 ℚ g := hpf
      _ ≤ (N : ℝ) * (m * archGauge3 ℚ g) * finGauge3 ℚ g :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left harch hNpos.le) hfin0
      _ = (N : ℝ) * m * (archGauge3 ℚ g * finGauge3 ℚ g) := by ring
      _ ≤ (N : ℝ) * m * gauge3 ℚ g := mul_le_mul_of_nonneg_left hprod (mul_nonneg hNpos.le hm0)
  have hNG : 0 < (N : ℝ) * gauge3 ℚ g := mul_pos hNpos (gauge3_pos ℚ g)
  rw [inv_le_iff_one_le_mul₀ hNG]
  calc (1 : ℝ) ≤ (N : ℝ) * m * gauge3 ℚ g := hkey
    _ = m * ((N : ℝ) * gauge3 ℚ g) := by ring

end Bound

end KcFirstMin

open LanglandsTunnell.CubicInduction in
theorem solution
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (N : ℕ) (hN : 0 < N) (ξ : Fin 3 → ℚ) (hξ : ξ ≠ 0)
    (hint : ∀ (j : Fin 3) (w : HeightOneSpectrum (𝓞 ℚ)),
      ((N : FiniteAdeleRing (𝓞 ℚ) ℚ) *
          (Matrix.vecMul (fun i => algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (ξ i))
            (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) j).2) w ∈ w.adicCompletionIntegers ℚ) :
    ∃ j : Fin 3, ((N : ℝ) * gauge3 ℚ g)⁻¹ ≤
      ‖(Matrix.vecMul (fun i => algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (ξ i))
          (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) j).1 Rat.infinitePlace‖ :=
  KcFirstMin.exists_le_norm g ξ N hN hξ hint

end

end S_LanglandsTunnell_CubicInduction_exists_inv_mul_gauge3_le_norm_vecMul_of_forall_mem_adicCompletionIntegers
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_inv_mul_gauge3_le_norm_vecMul_of_forall_mem_adicCompletionIntegers (solution)
