-- Prove2me | solution 1 for KanCombine.Optimal.eq_A13
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-27T00:25:52.746333+00:00
-- url     : https://prove2.me/submissions/6263bd66-2f63-4469-94ec-6bdbe54ac7a5

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting
import Definitions.Def_KanCombine_Optimal_Model
import Definitions.Def_MuirheadMST_Wishart
import Theorems.Thm_MathlibGap_multivariateGaussian_map_toEuclideanLin
import Theorems.Thm_GaussianMatrix_inverse_wishart_mean
import Theorems.Thm_GaussianMatrix_inverse_wishart_frobenius_moment
import Theorems.Thm_MuirheadMST_wishart_density

-- vendored from Solutions.Lib.Gaussian
section Solutions_Lib_Gaussian

/-! Shared helpers (Gaussian). `import Solutions.Lib.Gaussian`, then `open P2mLib.Gaussian`;
`p2m check` and `p2m verify` inline this file before submitting. -/

-- extracted from Sol_bartlett_decomposition.lean by `p2m lib extract`
noncomputable section

open MeasureTheory ProbabilityTheory WithLp
open MuirheadMST

namespace P2mLib.Gaussian

/-- Transposing an array of i.i.d. `N(0,1)` entries preserves its law. -/
lemma transpose_mp (m n : ℕ) :
    MeasurePreserving (fun (x : Fin n → Fin m → ℝ) j i => x i j)
      (Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1)
      (Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1) := by
  have hm : Measurable (fun (x : Fin n → Fin m → ℝ) j i => x i j) := by fun_prop
  refine ⟨hm, (Measure.pi_eq_generateFrom (fun _ => generateFrom_pi) (fun _ => isPiSystem_pi)
    (fun _ => Measure.FiniteSpanningSetsIn.pi fun _ => (gaussianReal 0 1).toFiniteSpanningSetsIn)
    fun s hs => ?_).symm⟩
  choose u hu hus using hs
  have hs' : s = fun j => Set.pi Set.univ (u j) := funext fun j => (hus j).symm
  subst hs'
  have hu' : ∀ j i, MeasurableSet (u j i) := fun j i => hu j i (Set.mem_univ _)
  have hpre : (fun (x : Fin n → Fin m → ℝ) j i => x i j) ⁻¹'
      Set.pi Set.univ (fun j => Set.pi Set.univ (u j)) =
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => u j i)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    exact forall_comm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi fun j => MeasurableSet.univ_pi (hu' j)), hpre,
    Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact Finset.prod_comm

end P2mLib.Gaussian

end

end Solutions_Lib_Gaussian

-- vendored from Solutions.Lib.Kan
section Solutions_Lib_Kan

/-! Shared results for the Kan et al. portfolio mission (namespace `P2mLib.Kan`); see docs/missions/kan.md.
`import Solutions.Lib.Kan`; `p2m check`/`verify` inline this file before submitting.
- `gmv W = W⁻¹e/(eᵀW⁻¹e)`, `zim W = W⁻¹(I - e gmv(W)ᵀ)`.
- `sample_law`: (µ̂, hΣ̂) ~ N(µ, Σ/h) ⊗ W_N(h-1, Σ) for an i.i.d. Gaussian sample.
- `wishart_inv_moments`: E V⁻¹ and E V⁻² for V ~ W_p(n, I).
- `gmv_moments`: moments of gmv and zim for W ~ W_N(n, Σ). -/

-- from Theorems/Local_kan_defs.lean
section KanDefs
open Matrix

namespace P2mLib.Kan

/-- The global-minimum-variance weights `w(W) = W⁻¹e / (eᵀW⁻¹e)` of a matrix `W`. -/
noncomputable def gmv {N : ℕ} (W : Matrix (Fin N) (Fin N) ℝ) : Fin N → ℝ :=
  ((fun _ => (1 : ℝ)) ⬝ᵥ (W⁻¹ *ᵥ fun _ => 1))⁻¹ • (W⁻¹ *ᵥ fun _ => 1)

/-- `Q(W) = W⁻¹(I - e w(W)ᵀ)`, the matrix of the zero-investment portfolio. -/
noncomputable def zim {N : ℕ} (W : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  W⁻¹ * (1 - vecMulVec (fun _ => 1) (gmv W))

end P2mLib.Kan

end KanDefs

-- from Sol_kan_K1.lean
section kan_K1

/-! Muirhead Thm 3.1.2 via the Helmert transformation: for an i.i.d. `N(µ, Σ)` sample of size `n + 1`,
the sample mean and `(n+1)` times the sample covariance have law `N(µ, Σ/(n+1)) ⊗ W_N(n, Σ)`.
Mixing the centred rows by an orthogonal `H` with last row `e/√(n+1)` keeps them i.i.d. `N(0, Σ)`;
the last mixed row is `√(n+1)` times the centred mean, the other `n` rows have Gram matrix the scatter matrix. -/

open MeasureTheory ProbabilityTheory RiskEU.OOSUVar WithLp
open scoped Matrix MatrixOrder

noncomputable section

namespace KanK1

abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- Mixing the rows of a sample by a matrix `H`: row `s` of the result is `∑ t, H s t • z t`. -/
def mix {h N : ℕ} (H : Matrix (Fin h) (Fin h) ℝ) (z : Fin h → E N) : Fin h → E N :=
  fun s => ∑ t, H s t • z t

lemma measurable_mix {h N : ℕ} (H : Matrix (Fin h) (Fin h) ℝ) : Measurable (mix (N := N) H) := by
  unfold mix; fun_prop

/-- Transposing an array of i.i.d. `N(0,1)` entries preserves its law. -/
lemma transpose_mp (m n : ℕ) :
    MeasurePreserving (fun (x : Fin n → Fin m → ℝ) j i => x i j)
      (Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1)
      (Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1) := by
  have hm : Measurable (fun (x : Fin n → Fin m → ℝ) j i => x i j) := by fun_prop
  refine ⟨hm, (Measure.pi_eq_generateFrom (fun _ => generateFrom_pi) (fun _ => isPiSystem_pi)
    (fun _ => Measure.FiniteSpanningSetsIn.pi fun _ => (gaussianReal 0 1).toFiniteSpanningSetsIn)
    fun s hs => ?_).symm⟩
  choose u hu hus using hs
  have hs' : s = fun j => Set.pi Set.univ (u j) := funext fun j => (hus j).symm
  subst hs'
  have hu' : ∀ j i, MeasurableSet (u j i) := fun j i => hu j i (Set.mem_univ _)
  have hpre : (fun (x : Fin n → Fin m → ℝ) j i => x i j) ⁻¹'
      Set.pi Set.univ (fun j => Set.pi Set.univ (u j)) =
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => u j i)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    exact forall_comm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi fun j => MeasurableSet.univ_pi (hu' j)), hpre,
    Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact Finset.prod_comm

/-- An orthogonal matrix as a linear isometry of `ℝʰ`. -/
def rot {h : ℕ} (H : Matrix (Fin h) (Fin h) ℝ) (hH : Hᵀ * H = 1) : E h ≃ₗᵢ[ℝ] E h :=
  ((Matrix.toEuclideanLin H).isometryOfInner fun x y => by
    simp only [Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hH,
      Matrix.vecMul_one]).toLinearIsometryEquiv rfl

/-- Mixing i.i.d. standard Gaussian rows by an orthogonal matrix preserves their law: in column
form, the mixing is the rotation `H` applied to each (standard Gaussian) column. -/
lemma mix_std {h N : ℕ} (H : Matrix (Fin h) (Fin h) ℝ) (hH : Hᵀ * H = 1) :
    MeasurePreserving (mix H) (Measure.pi fun _ : Fin h => stdGaussian (E N))
      (Measure.pi fun _ => stdGaussian (E N)) := by
  have hA : ∀ k l : ℕ, MeasurePreserving (fun (x : Fin k → Fin l → ℝ) i => toLp 2 (x i))
      (Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1)
      (Measure.pi fun _ => stdGaussian (E l)) := fun k l =>
    measurePreserving_pi _ _ fun _ => ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  -- transposition between `h` rows in `ℝᴺ` and `N` columns in `ℝʰ`, both ways
  have htr : ∀ k l : ℕ, MeasurePreserving (fun (z : Fin k → E l) j => toLp 2 (fun t => z t j))
      (Measure.pi fun _ => stdGaussian (E l)) (Measure.pi fun _ => stdGaussian (E k)) := by
    intro k l
    refine ⟨by fun_prop, ?_⟩
    rw [← (hA k l).map_eq, Measure.map_map (by fun_prop) (hA k l).measurable]
    exact ((hA l k).comp (transpose_mp l k)).map_eq
  have hρ : MeasurePreserving (fun (w : Fin N → E h) j => rot H hH (w j))
      (Measure.pi fun _ => stdGaussian (E h)) (Measure.pi fun _ => stdGaussian (E h)) :=
    measurePreserving_pi _ _ fun _ => ⟨(rot H hH).continuous.measurable, stdGaussian_map _⟩
  have hc := ((htr N h).comp hρ).comp (htr h N)
  convert hc using 1
  funext z s
  ext j
  simp [mix, rot, Matrix.mulVec, dotProduct]

/-- Same for i.i.d. `N(0, Σ)` rows: they are `√Σ` applied to standard ones, which commutes with mixing. -/
lemma mix_gauss {h N : ℕ} (H : Matrix (Fin h) (Fin h) ℝ) (hH : Hᵀ * H = 1)
    (S : Matrix (Fin N) (Fin N) ℝ) :
    MeasurePreserving (mix H) (Measure.pi fun _ : Fin h => multivariateGaussian 0 S)
      (Measure.pi fun _ => multivariateGaussian 0 S) := by
  set R : E N →L[ℝ] E N := Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)
  have hR : multivariateGaussian (0 : E N) S = (stdGaussian (E N)).map R := by
    simp [multivariateGaussian, R]
  let Rr : (Fin h → E N) → (Fin h → E N) := fun z t => R (z t)
  have hpi : Measure.pi (fun _ : Fin h => multivariateGaussian 0 S) =
      (Measure.pi fun _ => stdGaussian (E N)).map Rr := by
    rw [hR, Measure.pi_map_pi (f := fun _ => ⇑R) (fun _ => by fun_prop)]
  have hcomm : mix H ∘ Rr = Rr ∘ mix H := by
    funext z s
    simp [mix, Rr, map_sum, map_smul]
  refine ⟨measurable_mix H, ?_⟩
  rw [hpi, Measure.map_map (measurable_mix H) (by fun_prop), hcomm,
    ← Measure.map_map (by fun_prop) (measurable_mix H), (mix_std H hH).map_eq]

/-- A Helmert-type matrix: orthogonal, with last row `(1/√(n+1), …, 1/√(n+1))`. -/
lemma exists_helmert (n : ℕ) : ∃ H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
    Hᵀ * H = 1 ∧ ∀ t, H (Fin.last n) t = (Real.sqrt (n + 1))⁻¹ := by
  set u : E (n + 1) := toLp 2 (fun _ => (Real.sqrt (n + 1))⁻¹)
  have huu : inner ℝ u u = 1 := by
    have h0 : (0 : ℝ) < n + 1 := by positivity
    simp only [u, EuclideanSpace.inner_toLp_toLp, dotProduct, star_trivial, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_inv, Real.mul_self_sqrt h0.le]
    push_cast
    field_simp
  have hv : Orthonormal ℝ (({Fin.last n} : Set (Fin (n + 1))).domRestrict fun _ => u) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_singleton_iff] at hi hj
    subst hi hj
    simpa using huu
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨Matrix.of fun s t => b s t, ?_, ?_⟩
  · rw [mul_eq_one_comm]
    ext s s'
    have ho := b.orthonormal
    rw [orthonormal_iff_ite] at ho
    rw [Matrix.mul_apply, Matrix.one_apply, ← ho s s']
    simp [PiLp.inner_apply, mul_comm]
  · intro t
    simp [hb _ rfl, u]

lemma gauss_shift {N : ℕ} (m0 : E N) (S : Matrix (Fin N) (Fin N) ℝ) :
    (multivariateGaussian 0 S).map (fun x => m0 + x) = multivariateGaussian m0 S := by
  unfold multivariateGaussian
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp

lemma gauss_smul {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (hS : S.PosSemidef) (c : ℝ) :
    (multivariateGaussian 0 S).map (fun x : E N => c • x) = multivariateGaussian 0 ((c * c) • S) := by
  have h := MathlibGap.multivariateGaussian_map_toEuclideanLin S hS (c • (1 : Matrix (Fin N) (Fin N) ℝ))
  have e : (⇑(LinearMap.toContinuousLinearMap
      (Matrix.toEuclideanLin (c • (1 : Matrix (Fin N) (Fin N) ℝ))))) = fun x : E N => c • x := by
    funext x
    ext i
    simp
  rw [e] at h
  rw [h]
  congr 1
  simp [smul_smul]

lemma sqrt_inv_sq (n : ℕ) : (Real.sqrt (n + 1))⁻¹ * (Real.sqrt (n + 1))⁻¹ = ((n + 1 : ℕ) : ℝ)⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  push_cast
  rfl

/-- The Helmert identity for the sample mean. -/
lemma helmert_mean {n N : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hl : ∀ t, H (Fin.last n) t = (Real.sqrt (n + 1))⁻¹) (m0 : E N) (z : Fin (n + 1) → E N) :
    sampleMean (fun t => ofLp (m0 + z t)) = ofLp (m0 + (Real.sqrt (n + 1))⁻¹ • mix H z (Fin.last n)) := by
  have hc := sqrt_inv_sq n
  have h0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  funext i
  simp only [sampleMean, mix, hl, Pi.smul_apply, Finset.sum_apply, WithLp.ofLp_add, WithLp.ofLp_smul,
    WithLp.ofLp_sum, Pi.add_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.sum_const, Pi.mul_apply, Pi.natCast_apply,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← mul_assoc, hc]
  field_simp

/-- Two-sided form of the Helmert identity: dropping the last mixed coordinate removes the mean. -/
lemma helmert_key {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hH : Hᵀ * H = 1)
    (hl : ∀ t, H (Fin.last n) t = (Real.sqrt (n + 1))⁻¹) (a b : Fin (n + 1) → ℝ) :
    ∑ s : Fin n, (H *ᵥ a) s.castSucc * (H *ᵥ b) s.castSucc =
      ∑ t, (a t - ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ t', a t') * (b t - ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ t', b t') := by
  have hc := sqrt_inv_sq n
  have h0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hfull : (H *ᵥ a) ⬝ᵥ (H *ᵥ b) = a ⬝ᵥ b := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hH,
      Matrix.one_mulVec, dotProduct_comm]
  have hlast : ∀ v : Fin (n + 1) → ℝ, (H *ᵥ v) (Fin.last n) = (Real.sqrt (n + 1))⁻¹ * ∑ t, v t := by
    intro v
    simp [Matrix.mulVec, dotProduct, hl, Finset.mul_sum]
  simp only [dotProduct] at hfull
  rw [Fin.sum_univ_castSucc, hlast, hlast] at hfull
  have hexp : ∑ t, (a t - ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ t', a t') * (b t - ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ t', b t') =
      ∑ t, a t * b t - ((n + 1 : ℕ) : ℝ)⁻¹ * (∑ t, a t) * (∑ t, b t) := by
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  rw [hexp]
  linear_combination hfull - (∑ t, a t) * (∑ t, b t) * hc

/-- The Helmert identity for the scatter matrix. -/
lemma helmert_cov {n N : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hH : Hᵀ * H = 1)
    (hl : ∀ t, H (Fin.last n) t = (Real.sqrt (n + 1))⁻¹) (m0 : E N) (z : Fin (n + 1) → E N) :
    (fun i j => ((n + 1 : ℕ) : ℝ) * sampleCov (fun t => ofLp (m0 + z t)) i j) =
      MuirheadMST.gram (fun s : Fin n => mix H z s.castSucc) := by
  have h0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  funext i j
  have hk := helmert_key H hH hl (fun t => z t i) (fun t => z t j)
  have hmix : ∀ (s : Fin (n + 1)) (k : Fin N), (mix H z s).ofLp k = (H *ᵥ fun t => z t k) s := by
    intro s k
    simp [mix, Matrix.mulVec, dotProduct]
  simp only [MuirheadMST.gram, hmix]
  rw [hk]
  simp only [sampleCov, sampleMean, Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
    smul_eq_mul, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, WithLp.ofLp_add, Pi.add_apply,
    Finset.sum_add_distrib, Finset.sum_const, Pi.mul_apply, Pi.natCast_apply, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ h0, one_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  field_simp
  ring

end KanK1

open KanK1 in
theorem P2mLib.Kan.sample_law {N h : ℕ} (hh : 2 ≤ h) (M : Market N) (hS : M.Sigma.PosDef)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin h → Ω → EuclideanSpace ℝ (Fin N)) (hr : M.IsGaussianSample P r) :
    P.map (fun ω => (sampleMean (sampleData r ω), fun i j => (h : ℝ) * sampleCov (sampleData r ω) i j)) =
      ((multivariateGaussian (WithLp.toLp 2 M.mu) ((h : ℝ)⁻¹ • M.Sigma)).map (fun v => WithLp.ofLp v)).prod
        (MuirheadMST.wishart N (h - 1) M.Sigma) := by
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 1 := ⟨h - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  set m0 : E N := toLp 2 M.mu
  set c : ℝ := (Real.sqrt (n + 1))⁻¹
  obtain ⟨H, hH, hl⟩ := exists_helmert n
  let stat : (Fin (n + 1) → E N) → (Fin N → ℝ) × (Fin N → Fin N → ℝ) := fun x =>
    (sampleMean (fun t => ofLp (x t)), fun i j => ((n + 1 : ℕ) : ℝ) * sampleCov (fun t => ofLp (x t)) i j)
  let Ψ : (Fin (n + 1) → E N) → (Fin N → ℝ) × (Fin N → Fin N → ℝ) := fun y =>
    (ofLp (m0 + c • y (Fin.last n)), MuirheadMST.gram (fun s : Fin n => y s.castSucc))
  have hstat : Measurable stat := by
    refine Measurable.prodMk (by unfold sampleMean; fun_prop) ?_
    refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    simp only [sampleCov, sampleMean, Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
      smul_eq_mul, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply]
    fun_prop
  have hΨ : Measurable Ψ :=
    Measurable.prodMk (by fun_prop) (by unfold MuirheadMST.gram; fun_prop)
  have hjoint : P.map (fun ω t => r t ω) = Measure.pi fun _ => multivariateGaussian m0 M.Sigma := by
    rw [hr.1.map_fun_eq_pi_map fun t => (hr.2 t).aemeasurable]
    exact congrArg Measure.pi (funext fun t => (hr.2 t).map_eq)
  have hshift : Measure.pi (fun _ : Fin (n + 1) => multivariateGaussian m0 M.Sigma) =
      (Measure.pi fun _ => multivariateGaussian 0 M.Sigma).map (fun z t => m0 + z t) := by
    rw [Measure.pi_map_pi (f := fun _ x => m0 + x) (fun _ => by fun_prop)]
    simp_rw [gauss_shift]
  have hid : stat ∘ (fun z t => m0 + z t) = Ψ ∘ mix H := by
    funext z
    simp only [Function.comp_apply, stat, Ψ]
    rw [helmert_mean H hl m0 z, helmert_cov H hH hl m0 z]
  have hsplit : (Measure.pi fun _ : Fin (n + 1) => multivariateGaussian (0 : E N) M.Sigma).map Ψ =
      ((multivariateGaussian 0 M.Sigma).map (fun x : E N => ofLp (m0 + c • x))).prod
        (MuirheadMST.wishart N n M.Sigma) := by
    have hmp := measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => multivariateGaussian (0 : E N) M.Sigma) (Fin.last n)
    have hg : Measurable (MuirheadMST.gram (n := n) (m := N)) := by
      unfold MuirheadMST.gram; fun_prop
    have e : Ψ = Prod.map (fun x : E N => ofLp (m0 + c • x)) (MuirheadMST.gram (n := n) (m := N)) ∘
        MeasurableEquiv.piFinSuccAbove (fun _ => E N) (Fin.last n) := by
      funext y
      simp [Ψ, MeasurableEquiv.piFinSuccAbove_apply]
      rfl
    rw [e, ← Measure.map_map ((by fun_prop : Measurable fun x : E N => ofLp (m0 + c • x)).prodMap hg)
      hmp.measurable, hmp.map_eq, ← Measure.map_prod_map _ _ (by fun_prop) hg]
    rfl
  have hmean : (multivariateGaussian (0 : E N) M.Sigma).map (fun x : E N => ofLp (m0 + c • x)) =
      (multivariateGaussian m0 (((n + 1 : ℕ) : ℝ)⁻¹ • M.Sigma)).map (fun v => ofLp v) := by
    rw [← sqrt_inv_sq n, ← gauss_shift m0, ← gauss_smul _ hS.posSemidef,
      Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hlhs : P.map (fun ω => (sampleMean (sampleData r ω),
      fun i j => ((n + 1 : ℕ) : ℝ) * sampleCov (sampleData r ω) i j)) =
      (P.map (fun ω t => r t ω)).map stat := by
    rw [AEMeasurable.map_map_of_aemeasurable hstat.aemeasurable
      (aemeasurable_pi_lambda _ fun t => (hr.2 t).aemeasurable)]
    rfl
  rw [hlhs, hjoint, hshift, Measure.map_map hstat (by fun_prop), hid,
    ← Measure.map_map hΨ (measurable_mix H), (mix_gauss H hH M.Sigma).map_eq, hsplit, hmean]

end -- noncomputable section

end kan_K1

-- from Sol_kan_K2.lean
section kan_K2

open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators Matrix

noncomputable section

namespace KanK2

abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)

instance (k : ℕ) : SigmaFinite (stdGaussian (E k)) := IsFiniteMeasure.toSigmaFinite _

/-- Transposing an array of i.i.d. `N(0,1)` entries preserves its law. -/
lemma transpose_mp (m n : ℕ) :
    MeasurePreserving (fun (x : Fin n → Fin m → ℝ) j i => x i j)
      (Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1)
      (Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1) := by
  have hm : Measurable (fun (x : Fin n → Fin m → ℝ) j i => x i j) := by fun_prop
  refine ⟨hm, (Measure.pi_eq_generateFrom (fun _ => generateFrom_pi) (fun _ => isPiSystem_pi)
    (fun _ => Measure.FiniteSpanningSetsIn.pi fun _ => (gaussianReal 0 1).toFiniteSpanningSetsIn)
    fun s hs => ?_).symm⟩
  choose u hu hus using hs
  have hs' : s = fun j => Set.pi Set.univ (u j) := funext fun j => (hus j).symm
  subst hs'
  have hu' : ∀ j i, MeasurableSet (u j i) := fun j i => hu j i (Set.mem_univ _)
  have hpre : (fun (x : Fin n → Fin m → ℝ) j i => x i j) ⁻¹'
      Set.pi Set.univ (fun j => Set.pi Set.univ (u j)) =
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => u j i)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    exact forall_comm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi fun j => MeasurableSet.univ_pi (hu' j)), hpre,
    Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact Finset.prod_comm

/-- Columns of a standard Gaussian `p × n` matrix, read as `n` vectors of `ℝ^p`, and back. -/
lemma cols_mp (p n : ℕ) :
    MeasurePreserving (fun (z : Fin n → E p) (i : Fin p) (k : Fin n) => ofLp (z k) i)
      (Measure.pi fun _ => stdGaussian (E p)) (GaussianMatrix.gaussianMatrix p n) := by
  let τ : (Fin p → Fin n → ℝ) → (Fin n → E p) := fun G k => toLp 2 (fun i => G i k)
  have hA : MeasurePreserving (fun (x : Fin n → Fin p → ℝ) k => toLp 2 (x k))
      (Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1)
      (Measure.pi fun _ => stdGaussian (E p)) :=
    measurePreserving_pi _ _ fun _ => ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  have hτ : MeasurePreserving τ (GaussianMatrix.gaussianMatrix p n)
      (Measure.pi fun _ => stdGaussian (E p)) := hA.comp (transpose_mp n p)
  have hσm : Measurable (fun (z : Fin n → E p) (i : Fin p) (k : Fin n) => ofLp (z k) i) := by
    fun_prop
  refine ⟨hσm, ?_⟩
  rw [← hτ.map_eq, Measure.map_map hσm hτ.measurable]
  exact Measure.map_id

/-- `W_p(n, I)` is the law of `G Gᵀ` for a standard Gaussian `p × n` matrix `G`. -/
lemma wishart_eq_map (p n : ℕ) :
    MuirheadMST.wishart p n 1 = (GaussianMatrix.gaussianMatrix p n).map
      (fun G : Fin p → Fin n → ℝ => fun i j => ∑ k, G i k * G j k) := by
  have hφm : Measurable (fun G : Fin p → Fin n → ℝ => fun i j => ∑ k, G i k * G j k) := by
    fun_prop
  unfold MuirheadMST.wishart MuirheadMST.normalDataMatrix
  rw [multivariateGaussian_zero_one, ← (cols_mp p n).map_eq,
    Measure.map_map hφm (cols_mp p n).measurable]
  rfl

/-- An orthogonal matrix as a linear isometry of `ℝⁿ`. -/
def rotL {p : ℕ} (O : Matrix (Fin p) (Fin p) ℝ) (hO : Oᵀ * O = 1) : E p ≃ₗᵢ[ℝ] E p :=
  ((Matrix.toEuclideanLin O).isometryOfInner fun x y => by
    simp only [Matrix.toEuclideanLin_apply,
      EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hO,
      Matrix.vecMul_one]).toLinearIsometryEquiv rfl

/-- Left multiplication by an orthogonal matrix preserves the law of a Gaussian matrix. -/
lemma gauss_rot {p n : ℕ} (O : Matrix (Fin p) (Fin p) ℝ) (hO : Oᵀ * O = 1) :
    MeasurePreserving (fun (G : Fin p → Fin n → ℝ) i k => ∑ l, O i l * G l k)
      (GaussianMatrix.gaussianMatrix p n) (GaussianMatrix.gaussianMatrix p n) := by
  let τ : (Fin p → Fin n → ℝ) → (Fin n → E p) := fun G k => toLp 2 (fun i => G i k)
  have hτ : MeasurePreserving τ (GaussianMatrix.gaussianMatrix p n)
      (Measure.pi fun _ => stdGaussian (E p)) :=
    (measurePreserving_pi _ _ fun _ => ⟨by fun_prop, map_pi_eq_stdGaussian⟩).comp
      (transpose_mp n p)
  have hρ : MeasurePreserving (fun (z : Fin n → E p) k => rotL O hO (z k))
      (Measure.pi fun _ => stdGaussian (E p)) (Measure.pi fun _ => stdGaussian (E p)) :=
    measurePreserving_pi _ _ fun _ => ⟨(rotL O hO).continuous.measurable, stdGaussian_map _⟩
  have h := ((cols_mp p n).comp hρ).comp hτ
  convert h using 1
  funext G i k
  simp [τ, rotL, Matrix.mulVec, dotProduct]

/-- Entries of the inverse of a square array are measurable. -/
lemma measurable_inv_entry (p : ℕ) (i j : Fin p) :
    Measurable fun A : Fin p → Fin p → ℝ => (Matrix.of A)⁻¹ i j := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  have hc : Continuous fun A : Fin p → Fin p → ℝ => Matrix.of A := continuous_id
  exact (hc.matrix_det.measurable.inv).mul ((hc.matrix_adjugate.matrix_elem i j).measurable)

/-- The bound `|(Y Y)ᵢⱼ| ≤ ‖Y‖_F²`. -/
lemma abs_sq_entry_le {p : ℕ} (Y : Matrix (Fin p) (Fin p) ℝ) (i j : Fin p) :
    |(Y * Y) i j| ≤ GaussianMatrix.frobSq Y := by
  have h1 : ∑ k, Y i k ^ 2 ≤ GaussianMatrix.frobSq Y :=
    Finset.single_le_sum (f := fun i' => ∑ k, Y i' k ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : ∑ k, Y k j ^ 2 ≤ GaussianMatrix.frobSq Y :=
    Finset.sum_le_sum fun k _ => Finset.single_le_sum (f := fun j' => Y k j' ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h3 : |(Y * Y) i j| ≤ ∑ k, (Y i k ^ 2 + Y k j ^ 2) / 2 := by
    rw [Matrix.mul_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul]
    nlinarith [sq_nonneg (|Y i k| - |Y k j|), sq_abs (Y i k), sq_abs (Y k j)]
  rw [← Finset.sum_div, Finset.sum_add_distrib] at h3
  linarith

/-- `(G Gᵀ)⁻¹` transforms as `O (G Gᵀ)⁻¹ Oᵀ` under `G ↦ O G`, and so does its square. -/
lemma sq_inv_rot {p n : ℕ} (O : Matrix (Fin p) (Fin p) ℝ) (hO : Oᵀ * O = 1)
    (G : Matrix (Fin p) (Fin n) ℝ) :
    ((O * G) * (O * G)ᵀ)⁻¹ * ((O * G) * (O * G)ᵀ)⁻¹ =
      O * ((G * Gᵀ)⁻¹ * (G * Gᵀ)⁻¹) * Oᵀ := by
  have hO' : O * Oᵀ = 1 := mul_eq_one_comm.1 hO
  have h1 : (O * G) * (O * G)ᵀ = O * (G * Gᵀ) * Oᵀ := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have h2 : (O * (G * Gᵀ) * Oᵀ)⁻¹ = O * (G * Gᵀ)⁻¹ * Oᵀ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv hO,
      Matrix.inv_eq_left_inv hO', Matrix.mul_assoc]
  rw [h1, h2]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Oᵀ O, hO, Matrix.one_mul]

end KanK2

open KanK2 in
theorem P2mLib.Kan.wishart_inv_moments (p n : ℕ) (hn : p + 3 < n) :
    (∀ i j, Integrable (fun A : Fin p → Fin p → ℝ => (Matrix.of A)⁻¹ i j) (MuirheadMST.wishart p n 1)) ∧
    (∀ i j, Integrable (fun A : Fin p → Fin p → ℝ => ((Matrix.of A)⁻¹ * (Matrix.of A)⁻¹) i j)
      (MuirheadMST.wishart p n 1)) ∧
    Matrix.of (fun i j => ∫ A, (Matrix.of A)⁻¹ i j ∂(MuirheadMST.wishart p n 1)) =
      ((n : ℝ) - p - 1)⁻¹ • (1 : Matrix (Fin p) (Fin p) ℝ) ∧
    Matrix.of (fun i j => ∫ A, ((Matrix.of A)⁻¹ * (Matrix.of A)⁻¹) i j ∂(MuirheadMST.wishart p n 1)) =
      (((n : ℝ) - 1) / (((n : ℝ) - p) * ((n : ℝ) - p - 1) * ((n : ℝ) - p - 3))) •
        (1 : Matrix (Fin p) (Fin p) ℝ) := by
  set μ := GaussianMatrix.gaussianMatrix p n
  let φ : (Fin p → Fin n → ℝ) → (Fin p → Fin p → ℝ) := fun G i j => ∑ k, G i k * G j k
  have hφm : Measurable φ := by fun_prop
  have hW : MuirheadMST.wishart p n 1 = μ.map φ := wishart_eq_map p n
  have hInvM := measurable_inv_entry p
  have hSqM : ∀ i j, Measurable fun A : Fin p → Fin p → ℝ =>
      ((Matrix.of A)⁻¹ * (Matrix.of A)⁻¹) i j := by
    intro i j
    simp only [Matrix.mul_apply]
    exact Finset.measurable_sum _ fun k _ => (hInvM i k).mul (hInvM k j)
  obtain ⟨hMint, hMean⟩ := GaussianMatrix.inverse_wishart_mean (r := p) (k := n) (by omega)
  obtain ⟨hFint, hFrob⟩ :=
    GaussianMatrix.inverse_wishart_frobenius_moment (r := p) (k := n) (by omega)
  -- the squared inverse on the Gaussian side
  have hSqInt : ∀ i j, Integrable (fun G : Fin p → Fin n → ℝ =>
      ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ * (Matrix.of G * (Matrix.of G)ᵀ)⁻¹) i j) μ := by
    intro i j
    refine hFint.mono' ((hSqM i j).comp hφm).aestronglyMeasurable (ae_of_all _ fun G => ?_)
    rw [Real.norm_eq_abs]
    exact abs_sq_entry_le _ i j
  -- transfer to the Gaussian side
  have hT1 : ∀ i j, ∫ A, (Matrix.of A)⁻¹ i j ∂(MuirheadMST.wishart p n 1) =
      ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j ∂μ := fun i j => by
    rw [hW, integral_map hφm.aemeasurable (hInvM i j).aestronglyMeasurable]; rfl
  have hT2 : ∀ i j, ∫ A, ((Matrix.of A)⁻¹ * (Matrix.of A)⁻¹) i j ∂(MuirheadMST.wishart p n 1) =
      ∫ G, ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ * (Matrix.of G * (Matrix.of G)ᵀ)⁻¹) i j ∂μ :=
    fun i j => by
      rw [hW, integral_map hφm.aemeasurable (hSqM i j).aestronglyMeasurable]; rfl
  refine ⟨fun i j => ?_, fun i j => ?_, ?_, ?_⟩
  · rw [hW, integrable_map_measure (hInvM i j).aestronglyMeasurable hφm.aemeasurable]
    exact hMint i j
  · rw [hW, integrable_map_measure (hSqM i j).aestronglyMeasurable hφm.aemeasurable]
    exact hSqInt i j
  · ext i j
    rw [Matrix.of_apply, hT1, hMean, Matrix.smul_apply, smul_eq_mul, one_div]
  · let Wf : (Fin p → Fin n → ℝ) → Matrix (Fin p) (Fin p) ℝ := fun G =>
      (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ * (Matrix.of G * (Matrix.of G)ᵀ)⁻¹
    let M : Matrix (Fin p) (Fin p) ℝ := Matrix.of fun i j => ∫ G, Wf G i j ∂μ
    have hWfm : ∀ i j, Measurable fun G => Wf G i j := fun i j => (hSqM i j).comp hφm
    -- orthogonal invariance
    have hrot : ∀ O : Matrix (Fin p) (Fin p) ℝ, Oᵀ * O = 1 → ∀ i j,
        ∫ G, (O * Wf G * Oᵀ) i j ∂μ = M i j := by
      intro O hO i j
      have h : MeasurePreserving (fun (G : Fin p → Fin n → ℝ) i k => ∑ l, O i l * G l k) μ μ :=
        gauss_rot O hO
      have e : ∀ G, Wf (fun i k => ∑ l, O i l * G l k) = O * Wf G * Oᵀ :=
        fun G => sq_inv_rot O hO (Matrix.of G)
      show _ = ∫ G, Wf G i j ∂μ
      simp only [← e]
      conv_rhs => rw [← h.map_eq]
      rw [integral_map h.measurable.aemeasurable (hWfm i j).aestronglyMeasurable]
    have hoff : ∀ i j, i ≠ j → M i j = 0 := by
      intro i j hij
      let s : Fin p → ℝ := fun k => if k = i then -1 else 1
      have hs : (Matrix.diagonal s)ᵀ * Matrix.diagonal s = 1 := by
        rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1; funext k; simp only [s]; split_ifs <;> norm_num
      have h := hrot _ hs i j
      have e2 : ∀ G, (Matrix.diagonal s * Wf G * (Matrix.diagonal s)ᵀ) i j = -Wf G i j := by
        intro G
        simp [Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal, s,
          Ne.symm hij]
      simp only [e2, integral_neg] at h
      have h2 : M i j = ∫ G, Wf G i j ∂μ := rfl
      linarith
    have hdiag : ∀ i j, M i i = M j j := by
      intro i j
      let σ := Equiv.swap i j
      let P : Matrix (Fin p) (Fin p) ℝ := σ.toPEquiv.toMatrix
      have hP : Pᵀ * P = 1 := by
        rw [PEquiv.mul_toMatrix_toPEquiv]
        ext a b
        simp [P, PEquiv.toMatrix_apply, Matrix.one_apply, Equiv.toPEquiv_apply]
      have h := hrot _ hP i i
      have e2 : ∀ G, (P * Wf G * Pᵀ) i i = Wf G j j := by
        intro G
        rw [PEquiv.toMatrix_toPEquiv_mul, Matrix.mul_apply]
        simp [P, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, σ]
      simp only [e2] at h
      exact h.symm
    have htr : ∑ i, M i i = (p : ℝ) * ((n : ℝ) - 1)
          / (((n : ℝ) - p) * ((n : ℝ) - p - 1) * ((n : ℝ) - p - 3)) := by
      rw [← hFrob]
      simp only [M, Matrix.of_apply]
      rw [← integral_finsetSum _ fun i _ => hSqInt i i]
      refine integral_congr_ae (ae_of_all _ fun G => ?_)
      have hY : ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹)ᵀ = (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ := by
        simp only [Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_transpose]
      simp only [GaussianMatrix.frobSq, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      have hab := congrFun (congrFun hY a) b
      rw [Matrix.transpose_apply] at hab
      rw [hab, sq]
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp; ext i; exact i.elim0
    let i0 : Fin p := ⟨0, hp⟩
    have hsum : ∑ i, M i i = (p : ℝ) * M i0 i0 := by
      rw [Finset.sum_congr rfl fun i _ => hdiag i i0, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have hc : M i0 i0 = ((n : ℝ) - 1) / (((n : ℝ) - p) * ((n : ℝ) - p - 1) * ((n : ℝ) - p - 3)) := by
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
      refine mul_left_cancel₀ hp0 ?_
      rw [← hsum, htr, mul_div_assoc]
    ext i j
    rw [Matrix.of_apply, hT2, Matrix.smul_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, mul_one, ← hc, ← hdiag i i0]
      rfl
    · rw [Matrix.one_apply_ne hij, mul_zero]
      exact hoff i j hij

end -- noncomputable section

end kan_K2

-- from Sol_kan_K3.lean
section kan_K3

open MeasureTheory ProbabilityTheory Matrix

noncomputable section

namespace KanK3

/-! ### Algebra: GMV weights and `Q` for a general vector `e` -/

/-- `W⁻¹e / (eᵀW⁻¹e)`; `P2mLib.Kan.gmv` is the case `e = 1`. -/
def gE {N : ℕ} (e : Fin N → ℝ) (W : Matrix (Fin N) (Fin N) ℝ) : Fin N → ℝ :=
  (e ⬝ᵥ (W⁻¹ *ᵥ e))⁻¹ • (W⁻¹ *ᵥ e)

/-- `W⁻¹(I - e gE(W)ᵀ)`; `P2mLib.Kan.zim` is the case `e = 1`. -/
def zE {N : ℕ} (e : Fin N → ℝ) (W : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  W⁻¹ * (1 - vecMulVec e (gE e W))

lemma inv_congr {N : ℕ} (A G : Matrix (Fin N) (Fin N) ℝ) :
    (A * G * Aᵀ)⁻¹ = (A⁻¹)ᵀ * G⁻¹ * A⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv, Matrix.mul_assoc]

/-- Covariance of `gE` under a congruence `G ↦ A G Aᵀ` that sends `e` to a multiple of `f`. -/
lemma gE_congr {N : ℕ} {A G : Matrix (Fin N) (Fin N) ℝ} {e f : Fin N → ℝ} {c : ℝ} (hc : c ≠ 0)
    (he : A⁻¹ *ᵥ e = c • f) : gE e (A * G * Aᵀ) = c⁻¹ • ((A⁻¹)ᵀ *ᵥ gE f G) := by
  have h1 : (A * G * Aᵀ)⁻¹ *ᵥ e = c • ((A⁻¹)ᵀ *ᵥ (G⁻¹ *ᵥ f)) := by
    rw [inv_congr, ← mulVec_mulVec, ← mulVec_mulVec, he, mulVec_smul, mulVec_smul]
  have h2 : e ⬝ᵥ ((A⁻¹)ᵀ *ᵥ (G⁻¹ *ᵥ f)) = c * (f ⬝ᵥ (G⁻¹ *ᵥ f)) := by
    rw [dotProduct_mulVec, vecMul_transpose, he, smul_dotProduct, smul_eq_mul]
  simp only [gE, h1, dotProduct_smul, h2, smul_eq_mul, mulVec_smul, smul_smul]
  congr 1
  by_cases hq : f ⬝ᵥ (G⁻¹ *ᵥ f) = 0
  · simp [hq]
  · field_simp

lemma zE_congr {N : ℕ} {A G : Matrix (Fin N) (Fin N) ℝ} {e f : Fin N → ℝ} {c : ℝ} (hc : c ≠ 0)
    (he : A⁻¹ *ᵥ e = c • f) : zE e (A * G * Aᵀ) = (A⁻¹)ᵀ * zE f G * A⁻¹ := by
  rw [zE, zE, gE_congr hc he, inv_congr]
  have h : A⁻¹ * vecMulVec e (c⁻¹ • ((A⁻¹)ᵀ *ᵥ gE f G)) = vecMulVec f (gE f G) * A⁻¹ := by
    rw [mul_vecMulVec, he, vecMulVec_mul, ← vecMul_transpose, transpose_transpose]
    ext i j
    simp [vecMulVec_apply]
    field_simp
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc, h]

/-- `e₀ = (1, 0, …, 0)`. -/
abbrev e₀ {p : ℕ} : Fin (p + 1) → ℝ := Pi.single 0 1

/-- The `(p+1) × (p+1)` matrix `diag(0, B)`. -/
def ext {p : ℕ} (B : Matrix (Fin p) (Fin p) ℝ) : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ :=
  Matrix.of (Fin.cons 0 fun i => Fin.cons 0 (B i))

@[simp] lemma ext_zero_left {p : ℕ} (B : Matrix (Fin p) (Fin p) ℝ) (j) : ext B 0 j = 0 := rfl
@[simp] lemma ext_zero_right {p : ℕ} (B : Matrix (Fin p) (Fin p) ℝ) (i : Fin p) :
    ext B i.succ 0 = 0 := rfl
@[simp] lemma ext_succ {p : ℕ} (B : Matrix (Fin p) (Fin p) ℝ) (i j : Fin p) :
    ext B i.succ j.succ = B i j := rfl

/-- Block inverse: for symmetric invertible `G` with invertible lower block `V`,
`gE e₀ G = (1, -V⁻¹w)` and `zE e₀ G = diag(0, V⁻¹)`, `w` the first column below the corner. -/
lemma block {p : ℕ} (G : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ) (hG : IsUnit G.det)
    (hsym : Gᵀ = G) (hV : IsUnit (G.submatrix Fin.succ Fin.succ).det) :
    gE e₀ G = Fin.cons 1 (-((G.submatrix Fin.succ Fin.succ)⁻¹ *ᵥ fun k => G k.succ 0)) ∧
    zE e₀ G = ext (G.submatrix Fin.succ Fin.succ)⁻¹ := by
  set V := G.submatrix Fin.succ Fin.succ with hVdef
  set w : Fin p → ℝ := fun k => G k.succ 0 with hw
  set g : Fin (p + 1) → ℝ := Fin.cons 1 (-(V⁻¹ *ᵥ w)) with hg
  set s := G 0 0 - w ⬝ᵥ (V⁻¹ *ᵥ w) with hs
  have hrow : ∀ k : Fin p, G 0 k.succ = w k := fun k => congrFun (congrFun hsym k.succ) 0
  have hVV : V *ᵥ (V⁻¹ *ᵥ w) = w := by rw [mulVec_mulVec, mul_nonsing_inv _ hV, one_mulVec]
  have hGg : G *ᵥ g = s • e₀ := by
    funext i
    cases i using Fin.cases with
    | zero =>
      simp only [mulVec, dotProduct, Fin.sum_univ_succ, hg, Fin.cons_zero, Fin.cons_succ, hrow,
        Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, hs, Pi.neg_apply, mul_neg,
        Finset.sum_neg_distrib]
      ring
    | succ i =>
      have h1 : ∑ x, G i.succ x.succ * (V⁻¹ *ᵥ w) x = w i := congrFun hVV i
      have h2 : (G *ᵥ g) i.succ = G i.succ 0 * 1 + ∑ x, G i.succ x.succ * -(V⁻¹ *ᵥ w) x := by
        simp only [mulVec, dotProduct, Fin.sum_univ_succ, hg, Fin.cons_zero, Fin.cons_succ]
        rfl
      rw [h2]
      simp only [mul_neg, Finset.sum_neg_distrib, h1, Pi.smul_apply,
        Pi.single_eq_of_ne (Fin.succ_ne_zero i), smul_eq_mul, mul_zero, mul_one]
      exact sub_self _
  have hginv : G⁻¹ *ᵥ (G *ᵥ g) = g := by rw [mulVec_mulVec, nonsing_inv_mul _ hG, one_mulVec]
  have hs0 : s ≠ 0 := by
    intro h0
    rw [hGg, h0, zero_smul, mulVec_zero] at hginv
    have := congrFun hginv 0
    simp [hg] at this
  have hGe : G⁻¹ *ᵥ e₀ = s⁻¹ • g := by
    rw [hGg, mulVec_smul] at hginv
    rw [← hginv, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  have hgE : gE e₀ G = g := by
    rw [gE, hGe, dotProduct_smul, single_dotProduct, hg, Fin.cons_zero, smul_eq_mul, one_mul,
      mul_one, smul_smul, inv_inv, mul_inv_cancel₀ hs0, one_smul]
  refine ⟨hgE, ?_⟩
  have hVsym : (V⁻¹)ᵀ = V⁻¹ := by
    rw [transpose_nonsing_inv]
    congr 1
    ext i j
    exact congrFun (congrFun hsym i.succ) j.succ
  have hGX : G * ext V⁻¹ = 1 - vecMulVec e₀ g := by
    ext i j
    cases j using Fin.cases with
    | zero =>
      cases i using Fin.cases <;>
        simp [mul_apply, Fin.sum_univ_succ, vecMulVec_apply, hg, one_apply]
    | succ j =>
      cases i using Fin.cases with
      | zero =>
        have hsymE : ∀ a b, V⁻¹ b a = V⁻¹ a b := fun a b => congrFun (congrFun hVsym a) b
        simp only [mul_apply, Fin.sum_univ_succ, ext_zero_left, ext_succ, mul_zero, zero_add,
          hrow, Matrix.sub_apply, one_apply, vecMulVec_apply, Pi.single_eq_same, hg, Fin.cons_succ,
          Pi.neg_apply, one_mul, mulVec, dotProduct]
        rw [if_neg (Fin.succ_ne_zero j).symm, zero_sub, neg_neg]
        exact Finset.sum_congr rfl fun x _ => by rw [hsymE]; ring
      | succ i =>
        simp only [mul_apply, Fin.sum_univ_succ, ext_zero_left, ext_succ, mul_zero, zero_add,
          Matrix.sub_apply, one_apply, vecMulVec_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero i), zero_mul,
          sub_zero, Fin.succ_inj]
        have := congrFun (congrFun (mul_nonsing_inv V hV) i) j
        simp only [mul_apply, one_apply] at this
        exact this
  rw [zE, hgE, ← hGX, nonsing_inv_mul_cancel_left _ _ hG]

lemma dot_self_nonneg {p : ℕ} (v : Fin p → ℝ) : 0 ≤ v ⬝ᵥ v := by
  simpa using dotProduct_self_star_nonneg v

/-- Householder reflection: an orthogonal `H` with `H v = |v| e₀`. -/
lemma householder {p : ℕ} (v : Fin (p + 1) → ℝ) :
    ∃ H : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ, H * Hᵀ = 1 ∧ H *ᵥ v = Real.sqrt (v ⬝ᵥ v) • e₀ := by
  set r := Real.sqrt (v ⬝ᵥ v) with hr
  have hr2 : r * r = v ⬝ᵥ v := Real.mul_self_sqrt (dot_self_nonneg v)
  by_cases hu : v - r • e₀ = 0
  · exact ⟨1, by simp, by rw [one_mulVec]; exact sub_eq_zero.1 hu⟩
  set u := v - r • e₀ with hudef
  set d := u ⬝ᵥ u with hd
  have hd0 : d ≠ 0 := fun h => hu (dotProduct_self_eq_zero.1 h)
  have hdot : d = 2 * (u ⬝ᵥ v) := by
    simp only [hd, hudef, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      single_dotProduct, dotProduct_single, smul_eq_mul, one_mul, mul_one, Pi.single_eq_same,
      Pi.sub_apply, Pi.smul_apply]
    linear_combination hr2
  set M := vecMulVec u u with hM
  have hMM : M * M = d • M := by rw [hM, vecMulVec_mul, vecMul_vecMulVec, vecMulVec_smul]
  have hMt : Mᵀ = M := by rw [hM, transpose_vecMulVec]
  refine ⟨1 - (2 / d) • M, ?_, ?_⟩
  · rw [transpose_sub, transpose_one, transpose_smul, hMt, sub_mul, mul_sub, mul_sub, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul, smul_mul_smul_comm, hMM, smul_smul]
    have : 2 / d * (2 / d) * d = 2 / d + 2 / d := by field_simp; ring
    rw [this, add_smul]
    abel
  · rw [sub_mulVec, one_mulVec, smul_mulVec, hM, vecMulVec_mulVec, op_smul_eq_smul, smul_smul]
    have huv : u ⬝ᵥ v ≠ 0 := fun h => hd0 (by rw [hdot, h, mul_zero])
    have : 2 / d * (u ⬝ᵥ v) = 1 := by rw [hdot]; field_simp
    rw [this, one_smul, hudef]
    abel

open scoped MatrixOrder in
/-- A congruence factor `A Aᵀ = S` that sends `e = (1, …, 1)` to a nonzero multiple of `e₀`. -/
lemma exists_A {p : ℕ} {S : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ} (hS : S.PosDef) :
    ∃ (A : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ) (c : ℝ), IsUnit A.det ∧ A * Aᵀ = S ∧ c ≠ 0 ∧
      A⁻¹ *ᵥ (fun _ => 1) = c • e₀ := by
  set L := CFC.sqrt S with hL
  have hS0 : (0 : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ) ≤ S := hS.posSemidef.nonneg
  have hLL : L * L = S := CFC.sqrt_mul_sqrt_self S hS0
  have hLt : Lᵀ = L := by
    have h := (CFC.sqrt_nonneg S).isSelfAdjoint
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hLdet : IsUnit L.det := by
    have h := hS.det_pos
    rw [← hLL, det_mul] at h
    exact isUnit_iff_ne_zero.2 fun h0 => by rw [h0, zero_mul] at h; exact lt_irrefl _ h
  set v := L⁻¹ *ᵥ (fun _ => (1 : ℝ)) with hv
  have hv0 : v ≠ 0 := by
    intro h0
    have := congrArg (L *ᵥ ·) h0
    simp only [hv, mulVec_mulVec, mul_nonsing_inv _ hLdet, one_mulVec, mulVec_zero] at this
    simpa using congrFun this 0
  obtain ⟨H, hH, hHv⟩ := householder v
  have hH' : Hᵀ * H = 1 := mul_eq_one_comm.1 hH
  have hHdet : IsUnit H.det := by
    have := congrArg det hH
    rw [det_mul, det_one] at this
    exact IsUnit.of_mul_eq_one _ this
  refine ⟨L * Hᵀ, Real.sqrt (v ⬝ᵥ v), ?_, ?_, ?_, ?_⟩
  · rw [det_mul, det_transpose]; exact hLdet.mul hHdet
  · rw [transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc Hᵀ, hH',
      Matrix.one_mul, hLt, hLL]
  · exact (Real.sqrt_pos.2 (lt_of_le_of_ne (dot_self_nonneg v)
      (fun h => hv0 (dotProduct_self_eq_zero.1 h.symm)))).ne'
  · rw [Matrix.mul_inv_rev, inv_eq_left_inv hH, ← mulVec_mulVec, ← hv, hHv]

/-! ### Laws: Wishart matrices as Gram matrices of Gaussian columns -/

open MuirheadMST WithLp

/-- Standard Gaussian vector in `ℝⁿ`, as i.i.d. `N(0,1)` coordinates. -/
abbrev γ (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi fun _ => gaussianReal 0 1

/-- `m` i.i.d. standard Gaussian columns of length `n`. -/
abbrev μX (m n : ℕ) : Measure (Fin m → Fin n → ℝ) := Measure.pi fun _ => γ n

/-- Gram array `(j, k) ↦ ⟨X j, X k⟩` of the columns. -/
def gramA {m n : ℕ} (X : Fin m → Fin n → ℝ) : Fin m → Fin m → ℝ := fun j k => ∑ i, X j i * X k i

lemma measurable_gramA {m n : ℕ} : Measurable (gramA : (Fin m → Fin n → ℝ) → _) := by
  unfold gramA; fun_prop

lemma of_gramA {m n : ℕ} (X : Fin m → Fin n → ℝ) : Matrix.of (gramA X) = of X * (of X)ᵀ := by
  ext j k; simp [gramA, mul_apply]

/-- `W_m(n, I)` is the law of the Gram array of `m` i.i.d. standard Gaussian columns in `ℝⁿ`. -/
lemma wishart_one_eq (m n : ℕ) : wishart m n 1 = (μX m n).map gramA := by
  have hA : MeasurePreserving (fun (x : Fin n → Fin m → ℝ) i => toLp 2 (x i))
      (Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1)
      (Measure.pi fun _ => stdGaussian (EuclideanSpace ℝ (Fin m))) :=
    measurePreserving_pi _ _ fun _ => ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  have hgm : Measurable (MuirheadMST.gram : (Fin n → EuclideanSpace ℝ (Fin m)) → Fin m → Fin m → ℝ) := by
    unfold MuirheadMST.gram; fun_prop
  rw [wishart, normalDataMatrix, multivariateGaussian_zero_one, ← hA.map_eq,
    Measure.map_map hgm hA.measurable, ← (P2mLib.Gaussian.transpose_mp n m).map_eq,
    Measure.map_map (hgm.comp hA.measurable) (P2mLib.Gaussian.transpose_mp n m).measurable]
  congr 1

/-- `B ↦ A B Aᵀ` on arrays. -/
def congrA {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (B : Fin m → Fin m → ℝ) : Fin m → Fin m → ℝ :=
  fun i j => (A * Matrix.of B * Aᵀ) i j

lemma measurable_congrA {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) : Measurable (congrA A) := by
  unfold congrA
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply]
  fun_prop

/-- `W_m(n, A Aᵀ)` is the image of `W_m(n, I)` under `B ↦ A B Aᵀ`. -/
lemma wishart_congr {m n : ℕ} {A S : Matrix (Fin m) (Fin m) ℝ} (hA : A * Aᵀ = S) :
    wishart m n S = (wishart m n 1).map (congrA A) := by
  have hgm : Measurable (MuirheadMST.gram : (Fin n → EuclideanSpace ℝ (Fin m)) → Fin m → Fin m → ℝ) := by
    unfold MuirheadMST.gram; fun_prop
  have hL : Measurable (Matrix.toEuclideanLin A : EuclideanSpace ℝ (Fin m) → _) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  have hcomp : congrA A ∘ MuirheadMST.gram =
      MuirheadMST.gram ∘ (fun (Z : Fin n → EuclideanSpace ℝ (Fin m)) i => Matrix.toEuclideanLin A (Z i)) := by
    funext Z j k
    simp only [Function.comp_apply, congrA, MuirheadMST.gram, Matrix.mul_apply, Matrix.of_apply,
      Matrix.transpose_apply]
    change _ = ∑ i, (A *ᵥ ofLp (Z i)) j * (A *ᵥ ofLp (Z i)) k
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun a _ => ?_
    ring
  have hG : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) 1).map
      (Matrix.toEuclideanLin A) = multivariateGaussian 0 S := by
    have := MathlibGap.multivariateGaussian_map_toEuclideanLin (1 : Matrix (Fin m) (Fin m) ℝ)
      PosSemidef.one A
    rw [Matrix.mul_one, hA] at this
    exact this
  have : ∀ _ : Fin n, SigmaFinite ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) 1).map
      (Matrix.toEuclideanLin A)) := fun _ => by rw [hG]; infer_instance
  rw [wishart, wishart, normalDataMatrix, normalDataMatrix, Measure.map_map (measurable_congrA A) hgm,
    hcomp, ← Measure.map_map hgm (by fun_prop),
    Measure.pi_map_pi (f := fun _ => (Matrix.toEuclideanLin A : EuclideanSpace ℝ (Fin m) → _))
      (fun _ => hL.aemeasurable)]
  simp_rw [hG]

/-- A standard Wishart matrix with `m ≤ n` is almost surely invertible. -/
lemma ae_det_ne_zero {m n : ℕ} (hmn : m ≤ n) :
    ∀ᵐ A ∂(wishart m n 1), (Matrix.of A).det ≠ 0 := by
  have hmeas : Measurable (fun A : Fin m → Fin m → ℝ => (Matrix.of A).det) := by
    simp only [Matrix.det_apply, Matrix.of_apply]; fun_prop
  have hZ : MeasurableSet {A : Fin m → Fin m → ℝ | (Matrix.of A).det = 0} :=
    measurableSet_eq_fun hmeas measurable_const
  rw [ae_iff, wishart_density m n hmn 1 PosDef.one]
  simp only [ne_eq, not_not]
  rw [withDensity_apply _ hZ]
  refine (setLIntegral_congr_fun hZ fun A hA => ?_).trans (lintegral_zero)
  rw [if_neg fun h => h.det_pos.ne' hA]
  simp

/-- `∀ᵐ X`, the Gram matrix of `m ≤ n` Gaussian columns is positive definite. -/
lemma ae_posDef {m n : ℕ} (hmn : m ≤ n) :
    ∀ᵐ X ∂(μX m n), (of X * (of X)ᵀ).PosDef := by
  have h := ae_det_ne_zero (n := n) hmn
  rw [wishart_one_eq] at h
  filter_upwards [ae_of_ae_map measurable_gramA.aemeasurable h] with X hX
  rw [of_gramA] at hX
  have hpsd : (of X * (of X)ᵀ).PosSemidef := by
    simpa using posSemidef_self_mul_conjTranspose (of X)
  exact hpsd.posDef_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hX))

/-! ### Gaussian moments on `Ω = ℝⁿ × (ℝⁿ)^p` -/

/-- Matrices carry the product σ-algebra of their entries. -/
instance matMS (m k : ℕ) : MeasurableSpace (Matrix (Fin m) (Fin k) ℝ) := MeasurableSpace.pi

lemma measurable_invA {m : ℕ} : Measurable (fun A : Fin m → Fin m → ℝ => (Matrix.of A)⁻¹) := by
  have h : (fun A : Fin m → Fin m → ℝ => (Matrix.of A)⁻¹) =
      fun A => Ring.inverse (Matrix.of A).det • (Matrix.of A).adjugate := funext fun A => inv_def _
  rw [h]
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  refine Measurable.mul (Measurable.inv ?_) ?_
  · simp only [det_apply, of_apply]; fun_prop
  · have hc : Continuous fun A : Fin m → Fin m → ℝ => (Matrix.of A).adjugate :=
      Continuous.matrix_adjugate continuous_id
    exact ((continuous_apply j).comp ((continuous_apply i).comp hc)).measurable

lemma memLp_coord {n : ℕ} (i : Fin n) : MemLp (fun x : Fin n → ℝ => x i) 2 (γ n) :=
  (memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_measurePreserving
    (measurePreserving_eval (fun _ => gaussianReal 0 1) i)

lemma gauss_coord {n : ℕ} (i : Fin n) :
    Integrable (fun x : Fin n → ℝ => x i) (γ n) ∧ ∫ x, x i ∂(γ n) = 0 := by
  refine ⟨(memLp_coord i).integrable one_le_two, ?_⟩
  have hmp := measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i
  have := integral_map (μ := γ n) (f := fun y : ℝ => y) hmp.measurable.aemeasurable
    aestronglyMeasurable_id
  rw [hmp.map_eq, integral_id_gaussianReal] at this
  exact this.symm

lemma gauss_coord_mul {n : ℕ} (i j : Fin n) :
    Integrable (fun x : Fin n → ℝ => x i * x j) (γ n) ∧
      ∫ x, x i * x j ∂(γ n) = if i = j then 1 else 0 := by
  refine ⟨(memLp_coord i).integrable_mul (memLp_coord j), ?_⟩
  split_ifs with hij
  · subst hij
    have hmp := measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i
    have := integral_map (μ := γ n) (f := fun y : ℝ => y * y) hmp.measurable.aemeasurable
      (by fun_prop)
    rw [hmp.map_eq] at this
    rw [← show ∫ x : Fin n → ℝ, (fun y : ℝ => y * y) (Function.eval i x) ∂(γ n) =
      ∫ x, x i * x i ∂(γ n) from rfl, ← this]
    have hv := variance_fun_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_of_integral_eq_zero (by fun_prop) (by simp)] at hv
    simpa [sq] using hv
  · have hind : iIndepFun (fun k (x : Fin n → ℝ) => x k) (γ n) :=
      iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id
    rw [(hind.indepFun hij).integral_fun_mul_eq_mul_integral
      (measurable_pi_apply i).aestronglyMeasurable (measurable_pi_apply j).aestronglyMeasurable]
    simp [(gauss_coord i).2]

/-- The sample space: one Gaussian column `x` and `p` further Gaussian columns `Y`. -/
abbrev ν (p n : ℕ) : Measure ((Fin n → ℝ) × (Fin p → Fin n → ℝ)) := (γ n).prod (μX p n)

lemma sep {p n : ℕ} {f : (Fin n → ℝ) → ℝ} {g : (Fin p → Fin n → ℝ) → ℝ}
    (hf : Integrable f (γ n)) (hg : Integrable g (μX p n)) :
    Integrable (fun ω : (Fin n → ℝ) × (Fin p → Fin n → ℝ) => f ω.1 * g ω.2) (ν p n) ∧
      ∫ ω, f ω.1 * g ω.2 ∂(ν p n) = (∫ x, f x ∂(γ n)) * ∫ Y, g Y ∂(μX p n) :=
  ⟨hf.mul_prod hg, integral_prod_mul f g⟩

/-- Functions of `Y` alone. -/
lemma snd_moment {p n : ℕ} {g : (Fin p → Fin n → ℝ) → ℝ} (hg : Integrable g (μX p n)) :
    Integrable (fun ω : (Fin n → ℝ) × (Fin p → Fin n → ℝ) => g ω.2) (ν p n) ∧
      ∫ ω, g ω.2 ∂(ν p n) = ∫ Y, g Y ∂(μX p n) := by
  have h := sep (f := fun _ => (1 : ℝ)) (integrable_const 1) hg
  simp only [one_mul, integral_const, probReal_univ, smul_eq_mul] at h
  exact h

/-- Given `Y`, `B(Y) x` is centred. -/
lemma lin_moment {p n q : ℕ} {B : (Fin p → Fin n → ℝ) → Matrix (Fin q) (Fin n) ℝ}
    (hB : ∀ k i, Integrable (fun Y => B Y k i) (μX p n)) (k : Fin q) :
    Integrable (fun ω : (Fin n → ℝ) × (Fin p → Fin n → ℝ) => (B ω.2 *ᵥ ω.1) k) (ν p n) ∧
      ∫ ω, (B ω.2 *ᵥ ω.1) k ∂(ν p n) = 0 := by
  have h : (fun ω : (Fin n → ℝ) × (Fin p → Fin n → ℝ) => (B ω.2 *ᵥ ω.1) k) =
      fun ω => ∑ i, ω.1 i * B ω.2 k i := by
    funext ω; simp only [mulVec, dotProduct]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [h]
  refine ⟨integrable_finsetSum _ fun i _ => (sep (gauss_coord i).1 (hB k i)).1, ?_⟩
  rw [integral_finsetSum _ fun i _ => (sep (gauss_coord i).1 (hB k i)).1]
  simp [(sep (gauss_coord _).1 (hB k _)).2, (gauss_coord _).2]

/-- Given `Y`, `E[(B x)_k (B x)_l] = (B Bᵀ)_{kl}`. -/
lemma quad_moment {p n q : ℕ} {B : (Fin p → Fin n → ℝ) → Matrix (Fin q) (Fin n) ℝ}
    (hB : ∀ k l i j, Integrable (fun Y => B Y k i * B Y l j) (μX p n)) (k l : Fin q) :
    Integrable (fun ω : (Fin n → ℝ) × (Fin p → Fin n → ℝ) =>
        (B ω.2 *ᵥ ω.1) k * (B ω.2 *ᵥ ω.1) l) (ν p n) ∧
      ∫ ω, (B ω.2 *ᵥ ω.1) k * (B ω.2 *ᵥ ω.1) l ∂(ν p n) =
        ∫ Y, (B Y * (B Y)ᵀ) k l ∂(μX p n) := by
  have h : (fun ω : (Fin n → ℝ) × (Fin p → Fin n → ℝ) => (B ω.2 *ᵥ ω.1) k * (B ω.2 *ᵥ ω.1) l) =
      fun ω => ∑ i, ∑ j, (ω.1 i * ω.1 j) * (B ω.2 k i * B ω.2 l j) := by
    funext ω
    simp only [mulVec, dotProduct]
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hint : ∀ i j, Integrable (fun ω : (Fin n → ℝ) × (Fin p → Fin n → ℝ) =>
      (ω.1 i * ω.1 j) * (B ω.2 k i * B ω.2 l j)) (ν p n) := fun i j =>
    (sep (gauss_coord_mul i j).1 (hB k l i j)).1
  rw [h]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j, ?_⟩
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  simp_rw [integral_finsetSum _ fun j _ => hint _ j]
  simp only [fun i j => (sep (gauss_coord_mul i j).1 (hB k l i j)).2, (gauss_coord_mul _ _).2,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← integral_finsetSum _ fun i _ => hB k l i i]
  simp [mul_apply]

/-! ### The lower block `V = Y Yᵀ ~ W_p(n, I)` and the regression matrix `M = V⁻¹Y` -/

/-- `V⁻¹` for `V = Y Yᵀ`. -/
def Vi {p n : ℕ} (Y : Fin p → Fin n → ℝ) : Matrix (Fin p) (Fin p) ℝ := (Matrix.of (gramA Y))⁻¹

/-- `M = V⁻¹ Y`: given `Y`, the regression coefficient `V⁻¹ Y x` of the first column is `M x`. -/
def Mm {p n : ℕ} (Y : Fin p → Fin n → ℝ) : Matrix (Fin p) (Fin n) ℝ := Vi Y * Matrix.of Y

lemma measurable_Vi {p n : ℕ} : Measurable (Vi : (Fin p → Fin n → ℝ) → _) :=
  measurable_invA.comp measurable_gramA

lemma measurable_Mm {p n : ℕ} : Measurable (Mm : (Fin p → Fin n → ℝ) → _) := by
  have := measurable_Vi (p := p) (n := n)
  refine measurable_pi_lambda _ fun k => measurable_pi_lambda _ fun i => ?_
  simp only [Mm, mul_apply, of_apply]
  fun_prop

lemma Vi_symm {p n : ℕ} (Y : Fin p → Fin n → ℝ) : (Vi Y)ᵀ = Vi Y := by
  rw [Vi, transpose_nonsing_inv, of_gramA, transpose_mul, transpose_transpose]

lemma Vi_comm {p n : ℕ} (Y : Fin p → Fin n → ℝ) (k l : Fin p) : Vi Y l k = Vi Y k l :=
  congrFun (congrFun (Vi_symm Y) k) l

lemma Mm_mul_transpose {p n : ℕ} (Y : Fin p → Fin n → ℝ) : Mm Y * (Mm Y)ᵀ = Vi Y := by
  rw [Mm, transpose_mul, Vi_symm, Matrix.mul_assoc, ← Matrix.mul_assoc (of Y), ← of_gramA, Vi]
  by_cases h : IsUnit (of (gramA Y)).det
  · rw [mul_nonsing_inv _ h, Matrix.mul_one]
  · rw [nonsing_inv_apply_not_isUnit _ h, Matrix.zero_mul]

lemma sq_Mm_le {p n : ℕ} (Y : Fin p → Fin n → ℝ) (k : Fin p) (i : Fin n) :
    Mm Y k i ^ 2 ≤ Vi Y k k := by
  rw [← Mm_mul_transpose, mul_apply, sq]
  exact Finset.single_le_sum (f := fun j => Mm Y k j * (Mm Y)ᵀ j k)
    (fun j _ => mul_self_nonneg (Mm Y k j)) (Finset.mem_univ i)

lemma sq_Vi_le {p n : ℕ} (Y : Fin p → Fin n → ℝ) (k l : Fin p) :
    Vi Y k l ^ 2 ≤ (Vi Y * Vi Y) k k := by
  rw [mul_apply, sq]
  have h := Finset.single_le_sum (f := fun j => Vi Y k j * Vi Y k j)
    (fun j _ => mul_self_nonneg (Vi Y k j)) (Finset.mem_univ l)
  simpa only [Vi_comm Y k] using h

/-- `|f g| ≤ F + G` from `f² ≤ F`, `g² ≤ G`: integrability of products. -/
lemma integrable_mul_of_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g F G : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (hF : Integrable F μ)
    (hG : Integrable G μ) (hfF : ∀ ω, f ω ^ 2 ≤ F ω) (hgG : ∀ ω, g ω ^ 2 ≤ G ω) :
    Integrable (fun ω => f ω * g ω) μ := by
  refine (hF.add hG).mono' (hf.mul hg) (Filter.Eventually.of_forall fun ω => ?_)
  have h1 := hfF ω
  have h2 := hgG ω
  rw [Real.norm_eq_abs, abs_mul]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (|f ω| - |g ω|), sq_abs (f ω), sq_abs (g ω)]

/-- The inverse moments of `V ~ W_p(n, I)` (the K2 statement), read on `Y`. -/
lemma K2 {p n : ℕ} (hn : p + 3 < n) :
    (∀ k l, Integrable (fun Y => Vi Y k l) (μX p n) ∧
      ∫ Y, Vi Y k l ∂(μX p n) = ((n : ℝ) - p - 1)⁻¹ * (1 : Matrix (Fin p) (Fin p) ℝ) k l) ∧
    (∀ k l, Integrable (fun Y => (Vi Y * Vi Y) k l) (μX p n) ∧
      ∫ Y, (Vi Y * Vi Y) k l ∂(μX p n) =
        ((n : ℝ) - 1) / (((n : ℝ) - p) * ((n : ℝ) - p - 1) * ((n : ℝ) - p - 3)) *
          (1 : Matrix (Fin p) (Fin p) ℝ) k l) := by
  obtain ⟨h1, h2, h3, h4⟩ := P2mLib.Kan.wishart_inv_moments p n hn
  rw [wishart_one_eq] at h1 h2 h3 h4
  refine ⟨fun k l => ⟨?_, ?_⟩, fun k l => ⟨?_, ?_⟩⟩
  · exact (integrable_map_measure (h1 k l).aestronglyMeasurable
      measurable_gramA.aemeasurable).1 (h1 k l)
  · have := congrFun (congrFun h3 k) l
    simp only [of_apply, Matrix.smul_apply, smul_eq_mul] at this
    rw [← this, integral_map measurable_gramA.aemeasurable (h1 k l).aestronglyMeasurable]
    rfl
  · exact (integrable_map_measure (h2 k l).aestronglyMeasurable
      measurable_gramA.aemeasurable).1 (h2 k l)
  · have := congrFun (congrFun h4 k) l
    simp only [of_apply, Matrix.smul_apply, smul_eq_mul] at this
    rw [← this, integral_map measurable_gramA.aemeasurable (h2 k l).aestronglyMeasurable]
    rfl

lemma int_Mm {p n : ℕ} (hn : p + 3 < n) (k : Fin p) (i : Fin n) :
    Integrable (fun Y => Mm Y k i) (μX p n) := by
  have hm : Measurable fun Y => Mm Y k i := by have := measurable_Mm (p := p) (n := n); fun_prop
  have := integrable_mul_of_sq (μ := μX p n) hm.aestronglyMeasurable
    (measurable_const (a := (1 : ℝ))).aestronglyMeasurable ((K2 hn).1 k k).1 (integrable_const 1)
    (fun Y => sq_Mm_le Y k i) (fun _ => by norm_num)
  simpa using this

lemma int_MmMm {p n : ℕ} (hn : p + 3 < n) (k l : Fin p) (i j : Fin n) :
    Integrable (fun Y => Mm Y k i * Mm Y l j) (μX p n) := by
  have := measurable_Mm (p := p) (n := n)
  exact integrable_mul_of_sq (by fun_prop) (by fun_prop) ((K2 hn).1 k k).1 ((K2 hn).1 l l).1
    (fun Y => sq_Mm_le Y k i) (fun Y => sq_Mm_le Y l j)

lemma int_ViMm {p n : ℕ} (hn : p + 3 < n) (k : Fin p) (i : Fin n) :
    Integrable (fun Y => (Vi Y * Mm Y) k i) (μX p n) := by
  have := measurable_Mm (p := p) (n := n)
  have := measurable_Vi (p := p) (n := n)
  simp only [mul_apply]
  exact integrable_finsetSum _ fun l _ => integrable_mul_of_sq (by fun_prop) (by fun_prop)
    ((K2 hn).2 k k).1 ((K2 hn).1 l l).1 (fun Y => sq_Vi_le Y k l) (fun Y => sq_Mm_le Y l i)

/-! ### Standard moments: `W₀ ~ W_{p+1}(n, I)` split as first column and the rest -/

/-- The data matrix with first column `x` and further columns `Y`. -/
def consE (p n : ℕ) : (Fin n → ℝ) × (Fin p → Fin n → ℝ) ≃ᵐ (Fin (p + 1) → Fin n → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => Fin n → ℝ) 0).symm

lemma consE_apply {p n : ℕ} (ω : (Fin n → ℝ) × (Fin p → Fin n → ℝ)) :
    consE p n ω = Fin.cons ω.1 ω.2 := by
  funext j
  cases j using Fin.cases <;> simp [consE, MeasurableEquiv.piFinSuccAbove]

lemma consE_mp (p n : ℕ) : MeasurePreserving (consE p n) (ν p n) (μX (p + 1) n) :=
  (measurePreserving_piFinSuccAbove (fun _ : Fin (p + 1) => γ n) 0).symm _

/-- The standard Wishart matrix `W₀ = X Xᵀ` on `Ω`. -/
def Gm {p n : ℕ} (ω : (Fin n → ℝ) × (Fin p → Fin n → ℝ)) : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ :=
  of (consE p n ω) * (of (consE p n ω))ᵀ

lemma ext_mul {p : ℕ} (B C : Matrix (Fin p) (Fin p) ℝ) : ext B * ext C = ext (B * C) := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;> simp [mul_apply, Fin.sum_univ_succ]

lemma ext_mulVec {p : ℕ} (B : Matrix (Fin p) (Fin p) ℝ) (a : ℝ) (v : Fin p → ℝ) :
    ext B *ᵥ (Fin.cons a v : Fin (p + 1) → ℝ) = Fin.cons 0 (B *ᵥ v) := by
  funext i
  cases i using Fin.cases <;> simp [mulVec, dotProduct, Fin.sum_univ_succ]

lemma block_one (p : ℕ) :
    gE e₀ (1 : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ) = Fin.cons 1 0 ∧
      zE e₀ (1 : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ) = ext 1 := by
  have hsub : (1 : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ).submatrix Fin.succ Fin.succ = 1 := by
    ext i j; simp [one_apply]
  have h := block (1 : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ) (by simp) (by simp) (by simp [hsub])
  simp only [hsub, inv_one] at h
  refine ⟨h.1.trans ?_, h.2⟩
  congr 1
  funext k
  simp [one_apply, Fin.succ_ne_zero]

/-- Almost surely, the block formulas hold for `W₀ = X Xᵀ`. -/
lemma ae_block {p n : ℕ} (hn : p + 1 ≤ n) :
    ∀ᵐ ω ∂(ν p n), gE e₀ (Gm ω) = Fin.cons 1 (-(Mm ω.2 *ᵥ ω.1)) ∧ zE e₀ (Gm ω) = ext (Vi ω.2) := by
  have h := ae_posDef (m := p + 1) hn
  rw [← (consE_mp p n).map_eq] at h
  filter_upwards [ae_of_ae_map (consE_mp p n).measurable.aemeasurable h] with ω hω
  have hsub : (Gm ω).submatrix Fin.succ Fin.succ = of (gramA ω.2) := by
    ext i j; simp [Gm, consE_apply, mul_apply, gramA]
  have hw : (fun k => Gm ω k.succ 0) = of ω.2 *ᵥ ω.1 := by
    funext k; simp [Gm, consE_apply, mul_apply, mulVec, dotProduct]
  have hpd : (Gm ω).PosDef := hω
  have hsym : (Gm ω)ᵀ = Gm ω := by rw [Gm, transpose_mul, transpose_transpose]
  have hV : IsUnit ((Gm ω).submatrix Fin.succ Fin.succ).det :=
    isUnit_iff_ne_zero.2 (hpd.submatrix (Fin.succ_injective _)).det_pos.ne'
  have hb := block (Gm ω) (isUnit_iff_ne_zero.2 hpd.det_pos.ne') hsym hV
  rw [hsub, hw, mulVec_mulVec] at hb
  exact hb

lemma of_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {F G : Ω → ℝ} {c : ℝ}
    (h : ∀ᵐ ω ∂μ, F ω = G ω) (hG : Integrable G μ ∧ ∫ ω, G ω ∂μ = c) :
    Integrable F μ ∧ ∫ ω, F ω ∂μ = c :=
  ⟨hG.1.congr (Filter.EventuallyEq.symm h), (integral_congr_ae h).trans hG.2⟩

lemma neg_moment {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {F : Ω → ℝ}
    (h : Integrable F μ ∧ ∫ ω, F ω ∂μ = 0) :
    Integrable (fun ω => -F ω) μ ∧ ∫ ω, -F ω ∂μ = 0 :=
  ⟨h.1.neg, by rw [integral_neg, h.2, neg_zero]⟩

lemma std_g {p n : ℕ} (hn : p + 3 < n) (j : Fin (p + 1)) :
    Integrable (fun ω => gE e₀ (Gm ω) j) (ν p n) ∧
      ∫ ω, gE e₀ (Gm ω) j ∂(ν p n) = gE e₀ 1 j := by
  rw [(block_one p).1]
  refine of_ae ((ae_block (by omega)).mono fun ω h => congrFun h.1 j) ?_
  cases j using Fin.cases with
  | zero => simp
  | succ j => simpa using neg_moment (lin_moment (fun k i => int_Mm hn k i) j)

lemma std_gg {p n : ℕ} (hn : p + 3 < n) (j k : Fin (p + 1)) :
    Integrable (fun ω => gE e₀ (Gm ω) j * gE e₀ (Gm ω) k) (ν p n) ∧
      ∫ ω, gE e₀ (Gm ω) j * gE e₀ (Gm ω) k ∂(ν p n) =
        gE e₀ 1 j * gE e₀ 1 k + ((n : ℝ) - p - 1)⁻¹ * zE e₀ 1 j k := by
  rw [(block_one p).1, (block_one p).2]
  refine of_ae ((ae_block (by omega)).mono fun ω h => by rw [h.1]) ?_
  cases j using Fin.cases <;> cases k using Fin.cases
  · simp
  · simpa using neg_moment (lin_moment (fun k i => int_Mm hn k i) _)
  · simpa using neg_moment (lin_moment (fun k i => int_Mm hn k i) _)
  · rename_i j k
    have h := quad_moment (fun k l i j => int_MmMm hn k l i j) j k
    simp only [Mm_mul_transpose, ((K2 hn).1 j k).2] at h
    simpa using h

lemma std_z {p n : ℕ} (hn : p + 3 < n) (j k : Fin (p + 1)) :
    Integrable (fun ω => zE e₀ (Gm ω) j k) (ν p n) ∧
      ∫ ω, zE e₀ (Gm ω) j k ∂(ν p n) = ((n : ℝ) - p - 1)⁻¹ * zE e₀ 1 j k := by
  rw [(block_one p).2]
  refine of_ae ((ae_block (by omega)).mono fun ω h => by rw [h.2]) ?_
  cases j using Fin.cases <;> cases k using Fin.cases
  · simp
  · simp
  · simp
  · rename_i j k
    have h := snd_moment (n := n) ((K2 hn).1 j k).1
    rw [((K2 hn).1 j k).2] at h
    simpa using h

lemma std_zz {p n : ℕ} (hn : p + 3 < n) (j k : Fin (p + 1)) :
    Integrable (fun ω => (zE e₀ (Gm ω) * zE e₀ (Gm ω)) j k) (ν p n) ∧
      ∫ ω, (zE e₀ (Gm ω) * zE e₀ (Gm ω)) j k ∂(ν p n) =
        ((n : ℝ) - 1) / (((n : ℝ) - p) * ((n : ℝ) - p - 1) * ((n : ℝ) - p - 3)) * zE e₀ 1 j k := by
  rw [(block_one p).2]
  refine of_ae ((ae_block (by omega)).mono fun ω h => by rw [h.2, ext_mul]) ?_
  cases j using Fin.cases <;> cases k using Fin.cases
  · simp
  · simp
  · simp
  · rename_i j k
    have h := snd_moment (n := n) ((K2 hn).2 j k).1
    rw [((K2 hn).2 j k).2] at h
    simpa using h

lemma std_zg {p n : ℕ} (hn : p + 3 < n) (j : Fin (p + 1)) :
    Integrable (fun ω => (zE e₀ (Gm ω) *ᵥ gE e₀ (Gm ω)) j) (ν p n) ∧
      ∫ ω, (zE e₀ (Gm ω) *ᵥ gE e₀ (Gm ω)) j ∂(ν p n) = 0 := by
  refine of_ae ((ae_block (by omega)).mono fun ω h => by
    rw [h.1, h.2, ext_mulVec, mulVec_neg, mulVec_mulVec]) ?_
  cases j using Fin.cases
  · simp
  · simpa [Mm] using neg_moment (lin_moment (fun k i => int_ViMm hn k i) _)

/-! ### Transfer to `W ~ W_N(n, S)` -/

lemma congr_vecMulVec {m : ℕ} (T : Matrix (Fin m) (Fin m) ℝ) (u : Fin m → ℝ) (i j : Fin m) :
    (T * vecMulVec u u * Tᵀ) i j = (T *ᵥ u) i * (T *ᵥ u) j := by
  rw [mul_vecMulVec, vecMulVec_mul, vecMul_transpose, vecMulVec_apply]

lemma mul_moment {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {F : Ω → ℝ} {a : ℝ} (r : ℝ)
    (h : Integrable F μ ∧ ∫ ω, F ω ∂μ = a) :
    Integrable (fun ω => r * F ω) μ ∧ ∫ ω, r * F ω ∂μ = r * a :=
  ⟨h.1.const_mul r, by rw [integral_const_mul, h.2]⟩

/-- Expectation commutes with a fixed linear map on random vectors. -/
lemma lin_vec {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {m q : ℕ} {v : Ω → Fin m → ℝ}
    (P : Matrix (Fin q) (Fin m) ℝ) {a : Fin m → ℝ}
    (hv : ∀ j, Integrable (fun ω => v ω j) μ ∧ ∫ ω, v ω j ∂μ = a j) (i : Fin q) :
    Integrable (fun ω => (P *ᵥ v ω) i) μ ∧ ∫ ω, (P *ᵥ v ω) i ∂μ = (P *ᵥ a) i := by
  simp only [mulVec, dotProduct]
  refine ⟨integrable_finsetSum _ fun j _ => (hv j).1.const_mul _, ?_⟩
  rw [integral_finsetSum _ fun j _ => (hv j).1.const_mul _]
  simp [integral_const_mul, (hv _).2]

/-- Expectation commutes with `M ↦ P M Q` on random matrices. -/
lemma lin_mat {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {m q : ℕ}
    {M : Ω → Matrix (Fin m) (Fin m) ℝ} (P : Matrix (Fin q) (Fin m) ℝ) (Q : Matrix (Fin m) (Fin q) ℝ)
    {a : Matrix (Fin m) (Fin m) ℝ}
    (hM : ∀ j k, Integrable (fun ω => M ω j k) μ ∧ ∫ ω, M ω j k ∂μ = a j k) (i l : Fin q) :
    Integrable (fun ω => (P * M ω * Q) i l) μ ∧ ∫ ω, (P * M ω * Q) i l ∂μ = (P * a * Q) i l := by
  simp only [mul_apply, Finset.sum_mul]
  have hint : ∀ k j, Integrable (fun ω => P i j * M ω j k * Q k l) μ := fun k j =>
    ((hM j k).1.const_mul (P i j)).mul_const (Q k l)
  refine ⟨integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => hint k j, ?_⟩
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => hint k j]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun j _ => hint k j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const, integral_const_mul, (hM j k).2]

/-- Pull an entry function of `W ~ W_{p+1}(n, S)`, `S = A Aᵀ`, back to `A W₀ Aᵀ` on `Ω`. -/
lemma pull {p n : ℕ} {A S : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ} (hA : A * Aᵀ = S)
    {F : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ → ℝ}
    (hF : Measurable fun B : Fin (p + 1) → Fin (p + 1) → ℝ => F (Matrix.of B)) {c : ℝ}
    (h : Integrable (fun ω => F (A * Gm ω * Aᵀ)) (ν p n) ∧ ∫ ω, F (A * Gm ω * Aᵀ) ∂(ν p n) = c) :
    Integrable (fun B => F (Matrix.of B)) (wishart (p + 1) n S) ∧
      ∫ B, F (Matrix.of B) ∂(wishart (p + 1) n S) = c := by
  have hφ : Measurable (fun X => congrA A (gramA X)) :=
    (measurable_congrA A).comp (measurable_gramA (m := p + 1) (n := n))
  have hW : wishart (p + 1) n S = (μX (p + 1) n).map (fun X => congrA A (gramA X)) := by
    rw [wishart_congr hA, wishart_one_eq, Measure.map_map (measurable_congrA A) measurable_gramA]
    rfl
  have hpt : ∀ ω, F (Matrix.of (congrA A (gramA (consE p n ω)))) = F (A * Gm ω * Aᵀ) := fun ω => by
    rw [Gm, ← of_gramA]; rfl
  rw [hW]
  constructor
  · rw [integrable_map_measure hF.aestronglyMeasurable hφ.aemeasurable,
      ← (consE_mp p n).integrable_comp_emb (consE p n).measurableEmbedding]
    convert h.1 using 1
    funext ω
    exact hpt ω
  · rw [integral_map hφ.aemeasurable hF.aestronglyMeasurable,
      ← (consE_mp p n).integral_comp' (fun X => F (Matrix.of (congrA A (gramA X))))]
    simp_rw [hpt]
    exact h.2

end KanK3

open KanK3 in
theorem P2mLib.Kan.gmv_moments (N n : ℕ) (hN : 2 ≤ N) (hn : N + 2 < n) (S : Matrix (Fin N) (Fin N) ℝ)
    (hS : S.PosDef) :
    let μW := MuirheadMST.wishart N n S
    let s2 := ((fun _ => (1 : ℝ)) ⬝ᵥ (S⁻¹ *ᵥ fun _ => 1))⁻¹
    (∀ i, Integrable (fun A => P2mLib.Kan.gmv (Matrix.of A) i) μW) ∧
    (∀ i j, Integrable (fun A => P2mLib.Kan.gmv (Matrix.of A) i * P2mLib.Kan.gmv (Matrix.of A) j) μW) ∧
    (∀ i j, Integrable (fun A => P2mLib.Kan.zim (Matrix.of A) i j) μW) ∧
    (∀ i j, Integrable (fun A => (P2mLib.Kan.zim (Matrix.of A) * S * P2mLib.Kan.zim (Matrix.of A)) i j) μW) ∧
    (∀ i, Integrable (fun A => ((P2mLib.Kan.zim (Matrix.of A) * S) *ᵥ P2mLib.Kan.gmv (Matrix.of A)) i) μW) ∧
    (fun i => ∫ A, P2mLib.Kan.gmv (Matrix.of A) i ∂μW) = P2mLib.Kan.gmv S ∧
    (∀ i j, ∫ A, P2mLib.Kan.gmv (Matrix.of A) i * P2mLib.Kan.gmv (Matrix.of A) j ∂μW =
      P2mLib.Kan.gmv S i * P2mLib.Kan.gmv S j + s2 / ((n : ℝ) - N) * P2mLib.Kan.zim S i j) ∧
    (∀ i j, ∫ A, P2mLib.Kan.zim (Matrix.of A) i j ∂μW = ((n : ℝ) - N)⁻¹ * P2mLib.Kan.zim S i j) ∧
    (∀ i j, ∫ A, (P2mLib.Kan.zim (Matrix.of A) * S * P2mLib.Kan.zim (Matrix.of A)) i j ∂μW =
      ((n : ℝ) - 1) / (((n : ℝ) - N + 1) * ((n : ℝ) - N) * ((n : ℝ) - N - 2)) * P2mLib.Kan.zim S i j) ∧
    (∀ i, ∫ A, ((P2mLib.Kan.zim (Matrix.of A) * S) *ᵥ P2mLib.Kan.gmv (Matrix.of A)) i ∂μW = 0) := by
  intro μW s2
  obtain ⟨p, rfl⟩ : ∃ p, N = p + 1 := ⟨N - 1, by omega⟩
  have hn' : p + 3 < n := by omega
  obtain ⟨A, c, hAdet, hAS, hc, hAe⟩ := exists_A hS
  set T := (A⁻¹)ᵀ with hT
  have hTt : Tᵀ = A⁻¹ := by rw [hT, transpose_transpose]
  have hS1 : S = A * 1 * Aᵀ := by rw [Matrix.mul_one, hAS]
  have hg : ∀ G, P2mLib.Kan.gmv (A * G * Aᵀ) = c⁻¹ • (T *ᵥ gE e₀ G) := fun G => gE_congr hc hAe
  have hz : ∀ G, P2mLib.Kan.zim (A * G * Aᵀ) = T * zE e₀ G * Tᵀ := fun G => by
    rw [hTt]; exact zE_congr hc hAe
  have hgS : P2mLib.Kan.gmv S = c⁻¹ • (T *ᵥ gE e₀ 1) := by rw [hS1]; exact hg 1
  have hzS : P2mLib.Kan.zim S = T * zE e₀ 1 * Tᵀ := by rw [hS1]; exact hz 1
  have hs2 : s2 = c⁻¹ * c⁻¹ := by
    have hSi : S⁻¹ = T * A⁻¹ := by rw [hS1, inv_congr, inv_one, Matrix.mul_one]
    simp only [s2, hSi, ← mulVec_mulVec, dotProduct_mulVec, hT, vecMul_transpose, hAe,
      smul_dotProduct, dotProduct_smul, single_dotProduct, Pi.single_eq_same, smul_eq_mul, mul_one]
    rw [mul_inv]
  have hTST : Tᵀ * S * T = 1 := by
    rw [hTt, ← hAS, hT, ← Matrix.mul_assoc, nonsing_inv_mul _ hAdet, Matrix.one_mul,
      ← transpose_mul, nonsing_inv_mul _ hAdet, transpose_one]
  have hinv := measurable_invA (m := p + 1)
  -- the five moment computations, each with its integrability
  have R1 : ∀ i, Integrable (fun B => P2mLib.Kan.gmv (Matrix.of B) i) μW ∧
      ∫ B, P2mLib.Kan.gmv (Matrix.of B) i ∂μW = P2mLib.Kan.gmv S i := fun i =>
    pull hAS (F := fun W => P2mLib.Kan.gmv W i) (by
        simp only [P2mLib.Kan.gmv, Pi.smul_apply, smul_eq_mul, dotProduct, mulVec]; fun_prop)
      (of_ae (Filter.Eventually.of_forall fun ω => by rw [hg, Pi.smul_apply, smul_eq_mul])
        (by rw [hgS, Pi.smul_apply, smul_eq_mul]; exact mul_moment c⁻¹ (lin_vec T (std_g hn') i)))
  have R2 : ∀ i j, Integrable (fun B => P2mLib.Kan.gmv (Matrix.of B) i *
      P2mLib.Kan.gmv (Matrix.of B) j) μW ∧
      ∫ B, P2mLib.Kan.gmv (Matrix.of B) i * P2mLib.Kan.gmv (Matrix.of B) j ∂μW =
        P2mLib.Kan.gmv S i * P2mLib.Kan.gmv S j + s2 / ((n : ℝ) - ↑(p + 1)) *
          P2mLib.Kan.zim S i j := fun i j =>
    pull hAS (F := fun W => P2mLib.Kan.gmv W i * P2mLib.Kan.gmv W j) (by
        simp only [P2mLib.Kan.gmv, Pi.smul_apply, smul_eq_mul, dotProduct, mulVec]; fun_prop)
      (of_ae (G := fun ω => c⁻¹ * c⁻¹ *
          (T * vecMulVec (gE e₀ (Gm ω)) (gE e₀ (Gm ω)) * Tᵀ) i j)
        (Filter.Eventually.of_forall fun ω => by
          rw [hg, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, congr_vecMulVec]
          ring)
        (by
          have h := mul_moment (c⁻¹ * c⁻¹) (lin_mat (M := fun ω => vecMulVec (gE e₀ (Gm ω))
            (gE e₀ (Gm ω))) T Tᵀ (a := vecMulVec (gE e₀ 1) (gE e₀ 1) +
              ((n : ℝ) - p - 1)⁻¹ • zE e₀ 1) (fun j k => by
                simp only [vecMulVec_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
                exact std_gg hn' j k) i j)
          convert h using 2
          rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.smul_apply, smul_eq_mul, congr_vecMulVec, hgS, hzS, hs2]
          simp only [Pi.smul_apply, smul_eq_mul]
          push_cast
          ring))
  have R3 : ∀ i j, Integrable (fun B => P2mLib.Kan.zim (Matrix.of B) i j) μW ∧
      ∫ B, P2mLib.Kan.zim (Matrix.of B) i j ∂μW =
        ((n : ℝ) - ↑(p + 1))⁻¹ * P2mLib.Kan.zim S i j := fun i j =>
    pull hAS (F := fun W => P2mLib.Kan.zim W i j) (by
        simp only [P2mLib.Kan.zim, P2mLib.Kan.gmv, Pi.smul_apply, smul_eq_mul, dotProduct, mulVec,
          mul_apply, Matrix.sub_apply, vecMulVec_apply]; fun_prop)
      (of_ae (G := fun ω => (T * zE e₀ (Gm ω) * Tᵀ) i j)
        (Filter.Eventually.of_forall fun ω => by rw [hz])
        (by
          have h := lin_mat (M := fun ω => zE e₀ (Gm ω)) T Tᵀ
            (a := ((n : ℝ) - p - 1)⁻¹ • zE e₀ 1) (fun j k => by
                simp only [Matrix.smul_apply, smul_eq_mul]
                exact std_z hn' j k) i j
          convert h using 2
          rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, hzS]
          push_cast
          ring))
  have R4 : ∀ i j, Integrable (fun B => (P2mLib.Kan.zim (Matrix.of B) * S *
      P2mLib.Kan.zim (Matrix.of B)) i j) μW ∧
      ∫ B, (P2mLib.Kan.zim (Matrix.of B) * S * P2mLib.Kan.zim (Matrix.of B)) i j ∂μW =
        ((n : ℝ) - 1) / (((n : ℝ) - ↑(p + 1) + 1) * ((n : ℝ) - ↑(p + 1)) *
          ((n : ℝ) - ↑(p + 1) - 2)) * P2mLib.Kan.zim S i j := fun i j =>
    pull hAS (F := fun W => (P2mLib.Kan.zim W * S * P2mLib.Kan.zim W) i j) (by
        simp only [P2mLib.Kan.zim, P2mLib.Kan.gmv, Pi.smul_apply, smul_eq_mul, dotProduct, mulVec,
          mul_apply, Matrix.sub_apply, vecMulVec_apply]; fun_prop)
      (of_ae (G := fun ω => (T * (zE e₀ (Gm ω) * zE e₀ (Gm ω)) * Tᵀ) i j)
        (Filter.Eventually.of_forall fun ω => by
          rw [hz]
          have : T * zE e₀ (Gm ω) * Tᵀ * S * (T * zE e₀ (Gm ω) * Tᵀ) =
              T * (zE e₀ (Gm ω) * zE e₀ (Gm ω)) * Tᵀ := by
            have h2 : ∀ X : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ, Tᵀ * S * (T * X) = X := fun X => by
              rw [← Matrix.mul_assoc, hTST, Matrix.one_mul]
            simp only [Matrix.mul_assoc] at h2 ⊢
            rw [h2]
          rw [this])
        (by
          have h := lin_mat (M := fun ω => zE e₀ (Gm ω) * zE e₀ (Gm ω)) T Tᵀ
            (a := (((n : ℝ) - 1) / (((n : ℝ) - p) * ((n : ℝ) - p - 1) * ((n : ℝ) - p - 3))) •
              zE e₀ 1) (fun j k => by
                simp only [Matrix.smul_apply, smul_eq_mul]
                exact std_zz hn' j k) i j
          convert h using 2
          rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, hzS]
          push_cast
          ring_nf))
  have R5 : ∀ i, Integrable (fun B => ((P2mLib.Kan.zim (Matrix.of B) * S) *ᵥ
      P2mLib.Kan.gmv (Matrix.of B)) i) μW ∧
      ∫ B, ((P2mLib.Kan.zim (Matrix.of B) * S) *ᵥ P2mLib.Kan.gmv (Matrix.of B)) i ∂μW = 0 :=
    fun i =>
    pull hAS (F := fun W => ((P2mLib.Kan.zim W * S) *ᵥ P2mLib.Kan.gmv W) i) (by
        simp only [P2mLib.Kan.zim, P2mLib.Kan.gmv, Pi.smul_apply, smul_eq_mul, dotProduct, mulVec,
          mul_apply, Matrix.sub_apply, vecMulVec_apply]; fun_prop)
      (of_ae (G := fun ω => c⁻¹ * (T *ᵥ (zE e₀ (Gm ω) *ᵥ gE e₀ (Gm ω))) i)
        (Filter.Eventually.of_forall fun ω => by
          rw [hz, hg]
          have : (T * zE e₀ (Gm ω) * Tᵀ * S) *ᵥ (c⁻¹ • (T *ᵥ gE e₀ (Gm ω))) =
              c⁻¹ • (T *ᵥ (zE e₀ (Gm ω) *ᵥ gE e₀ (Gm ω))) := by
            rw [mulVec_smul, mulVec_mulVec, mulVec_mulVec]
            congr 2
            have h2 : Tᵀ * (S * T) = 1 := by rw [← Matrix.mul_assoc, hTST]
            simp only [Matrix.mul_assoc]
            rw [h2, Matrix.mul_one]
          rw [this, Pi.smul_apply, smul_eq_mul])
        (by
          have h := mul_moment c⁻¹ (lin_vec T (std_zg hn') i)
          simpa [mulVec, dotProduct] using h))
  exact ⟨fun i => (R1 i).1, fun i j => (R2 i j).1, fun i j => (R3 i j).1, fun i j => (R4 i j).1,
    fun i => (R5 i).1, funext fun i => (R1 i).2, fun i j => (R2 i j).2, fun i j => (R3 i j).2,
    fun i j => (R4 i j).2, fun i => (R5 i).2⟩

end -- noncomputable section

end kan_K3

end Solutions_Lib_Kan

-- vendored from Solutions.Lib.MatrixProb
section Solutions_Lib_MatrixProb

/-! General matrix and measure helpers collected from accepted solutions (GEPP growth mission).
`import Solutions.Lib.MatrixProb`, then `open P2mLib.MatrixProb`; `p2m check`/`verify` inline this file.

- `map_compl_eq_zero`, `bind_compl_eq_zero`: a property every outcome has holds surely through `map`/`bind`,
  with no measurability of the map or kernel needed.
- `dot_mulVec_le_specNorm`: the Rayleigh bound `xᵀMx ≤ ‖M‖ xᵀx` (l2 operator norm).
- `quad_ge_of_eig`: `λ (u·v)² ≤ uᵀSu` for PSD `S` with unit eigenvector `v` of eigenvalue `λ`. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace P2mLib.MatrixProb

/-- A pushforward of a measure by a map into a measurable set gives its complement mass zero. -/
lemma map_compl_eq_zero {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (f : α → β) {G : Set β} (hG : MeasurableSet G) (hf : ∀ x, f x ∈ G) : μ.map f Gᶜ = 0 := by
  by_cases h : AEMeasurable f μ
  · rw [Measure.map_apply_of_aemeasurable h hG.compl]
    have : f ⁻¹' Gᶜ = ∅ := by ext x; simp [hf x]
    simp [this]
  · simp [Measure.map_of_not_aemeasurable h]

lemma bind_compl_eq_zero {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (κ : α → Measure β) {G : Set β} (hG : MeasurableSet G) (hκ : ∀ᵐ x ∂μ, κ x Gᶜ = 0) :
    μ.bind κ Gᶜ = 0 := by
  by_cases h : AEMeasurable κ μ
  · rw [Measure.bind_apply hG.compl h]
    simpa using lintegral_congr_ae hκ
  · simp [Measure.bind, Measure.map_of_not_aemeasurable h]

/-- Rayleigh bound: `xᵀ M x ≤ ‖M‖ |x|²` for the l2 operator norm. -/
lemma dot_mulVec_le_specNorm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    x ⬝ᵥ (M *ᵥ x) ≤ ‖M‖ * (x ⬝ᵥ x) := by
  have h := Matrix.l2_opNorm_mulVec M (WithLp.toLp 2 x)
  have hin := real_inner_le_norm (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))
    ((EuclideanSpace.equiv (Fin d) ℝ).symm (M *ᵥ x))
  have hxx : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ ^ 2 = x ⬝ᵥ x := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]; simp [dotProduct, sq]
  have hin' : x ⬝ᵥ (M *ᵥ x) = inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))
      ((EuclideanSpace.equiv (Fin d) ℝ).symm (M *ᵥ x)) := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  have hn0 := norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))
  simp only at h
  rw [hin', ← hxx]
  show _ ≤ ‖M‖ * _
  nlinarith

/-- For symmetric PSD `S` with `S v = λ v`, `|v| = 1`: `uᵀ S u ≥ λ (u·v)²`. -/
lemma quad_ge_of_eig {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) (v : Fin d → ℝ)
    (hv : v ⬝ᵥ v = 1) (lam : ℝ) (heig : S *ᵥ v = lam • v) (u : Fin d → ℝ) :
    lam * (u ⬝ᵥ v) ^ 2 ≤ u ⬝ᵥ (S *ᵥ u) := by
  set a := u ⬝ᵥ v
  set u' := u - a • v with hu'
  have hu'v : u' ⬝ᵥ v = 0 := by
    simp [hu', sub_dotProduct, smul_dotProduct, hv, a]
  have hsymm : S.transpose = S := hS.1
  have hSu : S *ᵥ u = S *ᵥ u' + (a * lam) • v := by
    rw [show u = u' + a • v by simp [hu'], Matrix.mulVec_add, Matrix.mulVec_smul, heig, smul_smul]
  have hvS : v ⬝ᵥ (S *ᵥ u') = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, heig, smul_dotProduct,
      dotProduct_comm, hu'v, smul_zero]
  have key : u ⬝ᵥ (S *ᵥ u) = u' ⬝ᵥ (S *ᵥ u') + lam * a ^ 2 := by
    rw [hSu]
    conv_lhs => rw [show u = u' + a • v by simp [hu']]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, hvS, hu'v, hv,
      smul_eq_mul]
    ring
  have := hS.dotProduct_mulVec_nonneg u'
  simp at this
  nlinarith

end P2mLib.MatrixProb

end Solutions_Lib_MatrixProb

-- vendored from Solutions.Lib.KanBridge
section Solutions_Lib_KanBridge

/-! Bridge from the Kan et al. milestones (A9-A13) to `P2mLib.Kan` (namespace `P2mLib.KanBridge`).
`import Solutions.Lib.KanBridge`; `p2m check`/`verify` inline this file.

- Algebra: `wHatG x = gmv (hΣ̂)`, `BHat x = h • zim (hΣ̂)` (`wHatG_eq`, `BHat_eq`); `zim` of a symmetric matrix is
  symmetric; the market constants in sum form (`muG_eq`, `psi2_eq`, `sigmaG2_eq`, `trace_eq`).
- `bilin_sum`: `u ⬝ᵥ (K *ᵥ v) = ∑ (i, j), u i * v j * K i j`; `dot_mulVec_left`: `(Km)ᵀw = mᵀ(Kᵀw)`.
- `gauss`, `law`: N(µ, Σ/h) on plain vectors and `law = gauss ⊗ W_N(h-1, Σ)`, with first and second moments
  of `gauss` (`gauss_moments`) and a.e. symmetry of the Wishart coordinate (`ae_symm`).
- `reduce`: a sample statistic that is `F (µ̂, hΣ̂)` with `F` a.e. a finite sum of products `a i m * b i W`
  is integrable with expectation `∑ i, E a i * E b i`. -/

section kan_bridge

open MeasureTheory ProbabilityTheory Matrix RiskEU.OOSUVar

noncomputable section

namespace P2mLib.KanBridge

open P2mLib.Kan

variable {N : ℕ}

/-! ### Algebra -/

/-- `(c • W)⁻¹ = c⁻¹ • W⁻¹` for `c ≠ 0`, singular `W` included. -/
lemma inv_smul_of_ne (W : Matrix (Fin N) (Fin N) ℝ) {c : ℝ} (hc : c ≠ 0) :
    (c • W)⁻¹ = c⁻¹ • W⁻¹ := by
  by_cases hW : IsUnit W.det
  · simpa [Units.smul_def] using inv_smul' W (Units.mk0 c hc) hW
  · have h2 : ¬ IsUnit (c • W).det := by
      rw [det_smul]; simp_all [isUnit_iff_ne_zero]
    rw [nonsing_inv_apply_not_isUnit W hW, nonsing_inv_apply_not_isUnit _ h2, smul_zero]

lemma gmv_smul (W : Matrix (Fin N) (Fin N) ℝ) {c : ℝ} (hc : c ≠ 0) : gmv (c • W) = gmv W := by
  unfold gmv
  rw [inv_smul_of_ne W hc, smul_mulVec, dotProduct_smul, smul_eq_mul, smul_smul, _root_.mul_inv_rev, inv_inv,
    mul_assoc, mul_inv_cancel₀ hc, mul_one]

lemma zim_smul (W : Matrix (Fin N) (Fin N) ℝ) {c : ℝ} (hc : c ≠ 0) : zim (c • W) = c⁻¹ • zim W := by
  unfold zim
  rw [gmv_smul W hc, inv_smul_of_ne W hc, smul_mul_assoc]

lemma of_hcov {h : ℕ} (x : Fin h → Fin N → ℝ) :
    (Matrix.of fun i j => (h : ℝ) * sampleCov x i j) = (h : ℝ) • sampleCov x := by
  ext i j; simp

/-- `ŵ_g = gmv (hΣ̂)`. -/
lemma wHatG_eq {h : ℕ} (hh : (h : ℝ) ≠ 0) (x : Fin h → Fin N → ℝ) :
    wHatG x = gmv (Matrix.of fun i j => (h : ℝ) * sampleCov x i j) := by
  rw [of_hcov, gmv_smul _ hh]; rfl

/-- `B̂ = h • zim (hΣ̂)`. -/
lemma BHat_eq {h : ℕ} (hh : (h : ℝ) ≠ 0) (x : Fin h → Fin N → ℝ) :
    BHat x = (h : ℝ) • zim (Matrix.of fun i j => (h : ℝ) * sampleCov x i j) := by
  rw [of_hcov, zim_smul _ hh, smul_smul, mul_inv_cancel₀ hh, one_smul]; rfl

/-- `zim W` is symmetric when `W` is. -/
lemma zim_symm (W : Matrix (Fin N) (Fin N) ℝ) (hW : Wᵀ = W) : (zim W)ᵀ = zim W := by
  have hWi : (W⁻¹)ᵀ = W⁻¹ := by rw [transpose_nonsing_inv, hW]
  have hz : zim W = W⁻¹ - ((fun _ => (1 : ℝ)) ⬝ᵥ (W⁻¹ *ᵥ fun _ => 1))⁻¹ •
      vecMulVec (W⁻¹ *ᵥ fun _ => 1) (W⁻¹ *ᵥ fun _ => 1) := by
    unfold zim gmv
    rw [mul_sub, mul_one, mul_vecMulVec, vecMulVec_smul]
  rw [hz, transpose_sub, transpose_smul, transpose_vecMulVec, hWi]

/-- `u ⬝ᵥ (K *ᵥ v)` as a sum over index pairs. -/
lemma bilin_sum (u v : Fin N → ℝ) (K : Matrix (Fin N) (Fin N) ℝ) :
    u ⬝ᵥ (K *ᵥ v) = ∑ p : Fin N × Fin N, u p.1 * v p.2 * K p.1 p.2 := by
  simp only [dotProduct, mulVec, Fintype.sum_prod_type, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Moving a matrix across a dot product. -/
lemma dot_mulVec_left (K : Matrix (Fin N) (Fin N) ℝ) (m w : Fin N → ℝ) : (K *ᵥ m) ⬝ᵥ w = m ⬝ᵥ (Kᵀ *ᵥ w) := by
  rw [dotProduct_comm, dotProduct_mulVec, dotProduct_comm, mulVec_transpose]

lemma sigma_symm {S : Matrix (Fin N) (Fin N) ℝ} (hS : S.PosDef) : Sᵀ = S := by
  have := hS.isHermitian; rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this

section Market

variable (M : Market N) (hN : 1 ≤ N) (hS : M.Sigma.PosDef)
include hN hS

lemma ones_pos : 0 < (fun _ => (1 : ℝ)) ⬝ᵥ (M.Sigma⁻¹ *ᵥ fun _ : Fin N => 1) := by
  have h1 : (fun _ : Fin N => (1 : ℝ)) ≠ 0 := fun h => by
    simpa using congrFun h ⟨0, hN⟩
  simpa using hS.inv.dotProduct_mulVec_pos h1

omit hN hS in
/-- `µ_g = w_gᵀµ`. -/
lemma muG_eq : M.muG = ∑ i, M.mu i * gmv M.Sigma i := by
  have : ∑ i, M.mu i * gmv M.Sigma i = M.mu ⬝ᵥ gmv M.Sigma := rfl
  rw [this]; unfold gmv Market.muG Market.sigmaG2 ones
  rw [dotProduct_smul, smul_eq_mul, mul_comm]

/-- `ψ² = µᵀBµ`. -/
lemma psi2_eq : M.psi2 = ∑ p : Fin N × Fin N, M.mu p.1 * M.mu p.2 * zim M.Sigma p.1 p.2 := by
  rw [← bilin_sum]
  have ha := (ones_pos M hN hS).ne'
  set a := (fun _ => (1 : ℝ)) ⬝ᵥ (M.Sigma⁻¹ *ᵥ fun _ : Fin N => 1)
  set u := M.Sigma⁻¹ *ᵥ fun _ : Fin N => (1 : ℝ)
  have hg : gmv M.Sigma = a⁻¹ • u := rfl
  have hZ : zim M.Sigma *ᵥ M.mu = M.Sigma⁻¹ *ᵥ M.mu - (a⁻¹ * (u ⬝ᵥ M.mu)) • u := by
    have hv : vecMulVec (fun _ : Fin N => (1 : ℝ)) (gmv M.Sigma) *ᵥ M.mu =
        (gmv M.Sigma ⬝ᵥ M.mu) • fun _ : Fin N => (1 : ℝ) := by
      ext i; simp [mulVec, vecMulVec, dotProduct]
    unfold zim
    rw [← mulVec_mulVec, sub_mulVec, one_mulVec, hv, mulVec_sub, mulVec_smul, hg, smul_dotProduct,
      smul_eq_mul]
  have hmuG : M.muG = (M.mu ⬝ᵥ u) * a⁻¹ := rfl
  have hs2 : M.sigmaG2 = a⁻¹ := rfl
  unfold Market.psi2
  rw [hZ, dotProduct_sub, dotProduct_smul, hmuG, hs2, dotProduct_comm u, smul_eq_mul]
  field_simp

/-- `w_gᵀΣw_g = σ²_g`. -/
lemma sigmaG2_eq :
    ∑ p : Fin N × Fin N, gmv M.Sigma p.1 * gmv M.Sigma p.2 * M.Sigma p.1 p.2 = M.sigmaG2 := by
  rw [← bilin_sum]
  have ha := (ones_pos M hN hS).ne'
  have hdet : IsUnit M.Sigma.det := (Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit
  have hg : M.Sigma *ᵥ gmv M.Sigma =
      ((fun _ => (1 : ℝ)) ⬝ᵥ (M.Sigma⁻¹ *ᵥ fun _ : Fin N => 1))⁻¹ • fun _ => 1 := by
    unfold gmv
    rw [mulVec_smul, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  rw [hg]; unfold gmv Market.sigmaG2
  rw [smul_dotProduct, dotProduct_smul, dotProduct_comm, smul_eq_mul, smul_eq_mul]
  field_simp
  rw [dotProduct_comm]; rfl

/-- `tr(ΣB) = N - 1`, as a sum over index pairs. -/
lemma trace_eq : ∑ p : Fin N × Fin N, M.Sigma p.1 p.2 * zim M.Sigma p.1 p.2 = (N : ℝ) - 1 := by
  have ha := (ones_pos M hN hS).ne'
  have hdet : IsUnit M.Sigma.det := (Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit
  have hSt : M.Sigmaᵀ = M.Sigma := sigma_symm hS
  have h1 : ∑ p : Fin N × Fin N, M.Sigma p.1 p.2 * zim M.Sigma p.1 p.2 = (M.Sigmaᵀ * zim M.Sigma).trace := by
    simp only [trace, diag, mul_apply, transpose_apply, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
  rw [h1, hSt]; unfold zim
  rw [← Matrix.mul_assoc, mul_nonsing_inv _ hdet, Matrix.one_mul, trace_sub, trace_one, trace_vecMulVec]
  unfold gmv
  rw [dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ ha]
  simp

end Market

/-! ### Laws and moments -/

/-- The Gaussian `N(m0, S)` on plain vectors. -/
def gaussV (m0 : Fin N → ℝ) (S : Matrix (Fin N) (Fin N) ℝ) : Measure (Fin N → ℝ) :=
  (multivariateGaussian (WithLp.toLp 2 m0) S).map fun v => WithLp.ofLp v

instance (m0 : Fin N → ℝ) (S : Matrix (Fin N) (Fin N) ℝ) : IsProbabilityMeasure (gaussV m0 S) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

instance (n : ℕ) (S : Matrix (Fin N) (Fin N) ℝ) : IsProbabilityMeasure (MuirheadMST.wishart N n S) := by
  unfold MuirheadMST.wishart MuirheadMST.normalDataMatrix
  exact Measure.isProbabilityMeasure_map (by unfold MuirheadMST.gram; fun_prop)

/-- First and second moments of `N(m0, S)`. -/
lemma gauss_moments (m0 : Fin N → ℝ) (S : Matrix (Fin N) (Fin N) ℝ) (hS : S.PosSemidef) :
    (∀ j, Integrable (fun m => m j) (gaussV m0 S)) ∧
    (∀ j l, Integrable (fun m => m j * m l) (gaussV m0 S)) ∧
    (∀ j, ∫ m, m j ∂gaussV m0 S = m0 j) ∧
    (∀ j l, ∫ m, m j * m l ∂gaussV m0 S = m0 j * m0 l + S j l) := by
  set G := multivariateGaussian (WithLp.toLp 2 m0) S
  have hof : AEMeasurable (fun v : EuclideanSpace ℝ (Fin N) => WithLp.ofLp v) G := by fun_prop
  have hL2 : ∀ j, MemLp (fun v : EuclideanSpace ℝ (Fin N) => v.ofLp j) 2 G := fun j =>
    (memLp_id_gaussianReal 2).comp_measurePreserving (measurePreserving_eval_multivariateGaussian hS)
  have hint : ∀ j l, Integrable (fun v : EuclideanSpace ℝ (Fin N) => v.ofLp j * v.ofLp l) G :=
    fun j l => (hL2 j).integrable_mul (hL2 l)
  have hmean : ∀ j, ∫ v, v.ofLp j ∂G = m0 j := fun j => by
    have hmp := measurePreserving_eval_multivariateGaussian (μ := WithLp.toLp 2 m0) hS (i := j)
    have := integral_map (μ := G) hmp.measurable.aemeasurable (f := id) aestronglyMeasurable_id
    rw [hmp.map_eq] at this
    simp only [id] at this
    rw [integral_id_gaussianReal] at this
    simpa using this.symm
  refine ⟨fun j => ?_, fun j l => ?_, fun j => ?_, fun j l => ?_⟩
  · exact (integrable_map_measure (measurable_pi_apply j).aestronglyMeasurable hof).2
      ((hL2 j).integrable one_le_two)
  · exact (integrable_map_measure (by fun_prop : Measurable fun m : Fin N → ℝ => m j * m l).aestronglyMeasurable
      hof).2 (hint j l)
  · rw [gaussV, integral_map hof (measurable_pi_apply j).aestronglyMeasurable]; exact hmean j
  · rw [gaussV, integral_map hof (f := fun m : Fin N → ℝ => m j * m l)
      (by fun_prop : Measurable fun m : Fin N → ℝ => m j * m l).aestronglyMeasurable]
    have hc := covariance_eval_multivariateGaussian (μ := WithLp.toLp 2 m0) hS j l
    rw [covariance_eq_sub (hL2 j) (hL2 l), hmean, hmean] at hc
    simp only [Pi.mul_apply] at hc
    linarith

/-- The law of `(µ̂, hΣ̂)`: `N(µ, Σ/h) ⊗ W_N(h-1, Σ)`. -/
def law (M : Market N) (h : ℕ) : Measure ((Fin N → ℝ) × (Fin N → Fin N → ℝ)) :=
  (gaussV M.mu ((h : ℝ)⁻¹ • M.Sigma)).prod (MuirheadMST.wishart N (h - 1) M.Sigma)

instance (M : Market N) (h : ℕ) : IsProbabilityMeasure (law M h) := by
  unfold law; infer_instance

/-- Wishart draws are symmetric. -/
lemma ae_symm (M : Market N) (h : ℕ) : ∀ᵐ z ∂law M h, (Matrix.of z.2)ᵀ = Matrix.of z.2 := by
  have hW : ∀ᵐ A ∂MuirheadMST.wishart N (h - 1) M.Sigma, A ∈ {A : Fin N → Fin N → ℝ | ∀ i j, A j i = A i j} := by
    rw [ae_iff]
    refine P2mLib.MatrixProb.map_compl_eq_zero _ _ ?_ ?_
    · simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
        measurableSet_eq_fun (by fun_prop) (by fun_prop)
    · intro Z i j; simp only [MuirheadMST.gram]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hmap : (law M h).map Prod.snd = MuirheadMST.wishart N (h - 1) M.Sigma := by
    rw [law, Measure.map_snd_prod]; simp
  rw [← hmap] at hW
  filter_upwards [ae_of_ae_map measurable_snd.aemeasurable hW] with z hz
  ext i j; exact hz i j

/-- `(µ̂, hΣ̂)` as a function of the sample. -/
def stat {h : ℕ} {Ω : Type*} (r : Fin h → Ω → EuclideanSpace ℝ (Fin N)) (ω : Ω) :
    (Fin N → ℝ) × (Fin N → Fin N → ℝ) :=
  (sampleMean (sampleData r ω), fun i j => (h : ℝ) * sampleCov (sampleData r ω) i j)

/-- Expectations of `F (µ̂, hΣ̂)` are integrals against `law`. -/
lemma transfer {h : ℕ} (hh : 2 ≤ h) (M : Market N) (hS : M.Sigma.PosDef)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin h → Ω → EuclideanSpace ℝ (Fin N)) (hr : M.IsGaussianSample P r)
    (F : (Fin N → ℝ) × (Fin N → Fin N → ℝ) → ℝ) (hF : Integrable F (law M h)) :
    Integrable (fun ω => F (stat r ω)) P ∧ ∫ ω, F (stat r ω) ∂P = ∫ z, F z ∂law M h := by
  have hlaw : P.map (stat r) = law M h := P2mLib.Kan.sample_law hh M hS P r hr
  have hae : AEMeasurable (stat r) P := by
    by_contra hc
    have := Measure.map_of_not_aemeasurable hc
    rw [hlaw] at this
    exact IsProbabilityMeasure.ne_zero (law M h) this
  rw [← hlaw] at hF ⊢
  exact ⟨(integrable_map_measure hF.aestronglyMeasurable hae).1 hF,
    (integral_map hae hF.aestronglyMeasurable).symm⟩

/-- The reduction used by every milestone: a sample statistic `f = F ∘ stat` with `F` a.e. equal to
`∑ i ∈ s, a i m * b i W` (integrable factors) has expectation `∑ i ∈ s, E a i * E b i`. -/
lemma reduce {h : ℕ} (hh : 2 ≤ h) (M : Market N) (hS : M.Sigma.PosDef)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin h → Ω → EuclideanSpace ℝ (Fin N)) (hr : M.IsGaussianSample P r)
    {ι : Type*} (s : Finset ι) (a : ι → (Fin N → ℝ) → ℝ) (b : ι → (Fin N → Fin N → ℝ) → ℝ)
    (ha : ∀ i ∈ s, Integrable (a i) (gaussV M.mu ((h : ℝ)⁻¹ • M.Sigma)))
    (hb : ∀ i ∈ s, Integrable (b i) (MuirheadMST.wishart N (h - 1) M.Sigma))
    (f : Ω → ℝ) (F : (Fin N → ℝ) × (Fin N → Fin N → ℝ) → ℝ) (hf : ∀ ω, f ω = F (stat r ω))
    (hF : F =ᵐ[law M h] fun z => ∑ i ∈ s, a i z.1 * b i z.2) :
    Integrable f P ∧ ∫ ω, f ω ∂P =
      ∑ i ∈ s, (∫ m, a i m ∂gaussV M.mu ((h : ℝ)⁻¹ • M.Sigma)) *
        ∫ A, b i A ∂MuirheadMST.wishart N (h - 1) M.Sigma := by
  have hsum : Integrable (fun z : (Fin N → ℝ) × (Fin N → Fin N → ℝ) => ∑ i ∈ s, a i z.1 * b i z.2) (law M h) :=
    integrable_finsetSum _ fun i hi => (ha i hi).mul_prod (hb i hi)
  obtain ⟨h1, h2⟩ := transfer hh M hS P r hr F (hsum.congr hF.symm)
  have hf' : f = fun ω => F (stat r ω) := funext hf
  subst hf'
  refine ⟨h1, ?_⟩
  rw [h2, integral_congr_ae hF]
  unfold law
  rw [integral_finsetSum s (f := fun i (z : (Fin N → ℝ) × (Fin N → Fin N → ℝ)) => a i z.1 * b i z.2) fun i hi => (ha i hi).mul_prod (hb i hi)]
  exact Finset.sum_congr rfl fun i _ => integral_prod_mul (a i) (b i)

end P2mLib.KanBridge

end -- noncomputable section

end kan_bridge

end Solutions_Lib_KanBridge

/-! (A13): `E[ŵ_gᵀΣŵ_z] = 0`. With `W = hΣ̂ ~ W_N(h-1, Σ)` independent of `µ̂ ~ N(µ, Σ/h)`,
`ŵ_g = gmv W` and `ŵ_z = h·Q µ̂` with `Q = zim W` and `Σ` symmetric, the statistic is `h µ̂ᵀ(QΣ gmv W)`,
whose expectation is `h µᵀ E[QΣ gmv W] = 0`. -/

open MeasureTheory ProbabilityTheory Matrix RiskEU.OOSUVar KanCombine.Optimal P2mLib.Kan P2mLib.KanBridge

theorem solution {N h : ℕ} (M : Market N) (hM : KanStanding M h)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin h → Ω → EuclideanSpace ℝ (Fin N)) (hr : M.IsGaussianSample P r) :
    Integrable (fun ω => sigGZt M (sampleData r ω)) P ∧
      ∫ ω, sigGZt M (sampleData r ω) ∂P = 0 := by
  obtain ⟨hN, hNh, hS, -⟩ := hM
  have hh0 : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨-, -, -, -, hzg, -, -, -, -, hEzg⟩ := gmv_moments N (h - 1) hN (by omega) M.Sigma hS
  obtain ⟨hm1, -, -, -⟩ := gauss_moments M.mu ((h : ℝ)⁻¹ • M.Sigma)
    (hS.posSemidef.smul (by positivity))
  have hred := reduce (by omega) M hS P r hr (Finset.univ : Finset (Fin N))
    (fun l m => (h : ℝ) * m l)
    (fun l A => ((zim (Matrix.of A) * M.Sigma) *ᵥ gmv (Matrix.of A)) l)
    (fun l _ => (hm1 l).const_mul _) (fun l _ => hzg l)
    (fun ω => sigGZt M (sampleData r ω))
    (fun z => gmv (Matrix.of z.2) ⬝ᵥ (M.Sigma *ᵥ (((h : ℝ) • zim (Matrix.of z.2)) *ᵥ z.1)))
    (fun ω => by rw [sigGZt, wHatZ, BHat_eq hh0, wHatG_eq hh0]; rfl)
    (by
      filter_upwards [ae_symm M h] with z hz
      rw [mulVec_mulVec, dotProduct_comm, dot_mulVec_left, transpose_mul, transpose_smul, zim_symm _ hz,
        sigma_symm hS, Matrix.smul_mul, smul_mulVec]
      simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun l _ => by ring)
  refine ⟨hred.1, ?_⟩
  rw [hred.2]
  simp [hEzg]
