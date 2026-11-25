-- Prove2me | solution 1 for John.exists_projection_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:14:18.245053+00:00
-- url     : https://prove2.me/submissions/4c7ae1bf-f2b8-4904-865d-293e92d03868

module
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_CompactConvexHull
public import Definitions.Def_BasicResults_JohnIngredients
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Seminorm
public import Mathlib.Topology.Order.Compact
public import Definitions.Def_BasicResults_John
public import Theorems.Thm_John_exists_johnPosition
public import Theorems.Thm_John_rankOneSA_apply
public import Theorems.Thm_John_norm_inner_le_of_contact
public import Theorems.Thm_John_sum_weight_inner_sq
public import Theorems.Thm_John_sum_weight_mul_le_sqrt
public import Theorems.Thm_John_john_decomposition
attribute [local simp] John.rankOneSA_apply
section
@[expose] public section
universe u
open scoped InnerProductSpace ComplexConjugate
open RCLike (re)
namespace John
variable {𝕜 : Type u} [RCLike 𝕜] {k : ℕ}
section DualProjection
variable {W : Type u} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
private lemma exists_riesz_repr (Φ : EuclideanSpace 𝕜 (Fin k) ≃L[𝕜] StrongDual 𝕜 W)
    (hΦ : ∀ z, ‖Φ z‖ ≤ ‖z‖) (v : W) :
    ∃ r : EuclideanSpace 𝕜 (Fin k), (∀ z, ⟪r, z⟫_𝕜 = (Φ z) v) ∧ ‖r‖ ≤ ‖v‖ := by
  set ℓ : EuclideanSpace 𝕜 (Fin k) →L[𝕜] 𝕜 :=
    ((NormedSpace.inclusionInDoubleDual 𝕜 W) v).comp
      (Φ : EuclideanSpace 𝕜 (Fin k) →L[𝕜] StrongDual 𝕜 W) with hℓ
  have hℓapply : ∀ z, ℓ z = (Φ z) v := fun z => rfl
  have hℓnorm : ‖ℓ‖ ≤ ‖v‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun z => ?_
    rw [hℓapply z]
    calc ‖(Φ z) v‖ ≤ ‖Φ z‖ * ‖v‖ := (Φ z).le_opNorm v
      _ ≤ ‖z‖ * ‖v‖ := mul_le_mul_of_nonneg_right (hΦ z) (norm_nonneg v)
      _ = ‖v‖ * ‖z‖ := mul_comm _ _
  refine ⟨(InnerProductSpace.toDual 𝕜 (EuclideanSpace 𝕜 (Fin k))).symm ℓ, fun z => ?_, ?_⟩
  · rw [InnerProductSpace.toDual_symm_apply]
    exact hℓapply z
  · rw [LinearIsometryEquiv.norm_map]
    exact hℓnorm
private lemma exists_witness_of_contact [FiniteDimensional 𝕜 W]
    (hkW : Module.finrank 𝕜 W = k)
    (Φ : EuclideanSpace 𝕜 (Fin k) ≃L[𝕜] StrongDual 𝕜 W)
    {q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))} (hqΦ : ∀ z, ‖Φ z‖ = q z)
    (u₀ : EuclideanSpace 𝕜 (Fin k)) (hu₀ : ∀ z, ‖⟪z, u₀⟫_𝕜‖ ≤ q z) :
    ∃ w : W, (∀ g : StrongDual 𝕜 W, g w = ⟪u₀, Φ.symm g⟫_𝕜) ∧ ‖w‖ ≤ 1 := by
  classical
  set T : W →L[𝕜] StrongDual 𝕜 (EuclideanSpace 𝕜 (Fin k)) :=
    (Φ : EuclideanSpace 𝕜 (Fin k) →L[𝕜] StrongDual 𝕜 W).flip with hT
  have hTapply : ∀ (v : W) (z : EuclideanSpace 𝕜 (Fin k)), T v z = Φ z v :=
    fun v z => ContinuousLinearMap.flip_apply _ z v
  have : FiniteDimensional 𝕜 (StrongDual 𝕜 (EuclideanSpace 𝕜 (Fin k))) :=
    Module.Finite.equiv
      (LinearMap.toContinuousLinearMap :
        ((EuclideanSpace 𝕜 (Fin k)) →ₗ[𝕜] 𝕜) ≃ₗ[𝕜] ((EuclideanSpace 𝕜 (Fin k)) →L[𝕜] 𝕜))
  have hkSD : Module.finrank 𝕜 (StrongDual 𝕜 (EuclideanSpace 𝕜 (Fin k))) = k := by
    rw [← (LinearMap.toContinuousLinearMap :
          ((EuclideanSpace 𝕜 (Fin k)) →ₗ[𝕜] 𝕜) ≃ₗ[𝕜]
            ((EuclideanSpace 𝕜 (Fin k)) →L[𝕜] 𝕜)).finrank_eq,
        Subspace.dual_finrank_eq, finrank_euclideanSpace_fin]
  have hTinj : Function.Injective
      (T : W →ₗ[𝕜] StrongDual 𝕜 (EuclideanSpace 𝕜 (Fin k))) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    refine norm_le_zero_iff.mp (NormedSpace.norm_le_dual_bound 𝕜 v le_rfl fun g => ?_)
    have hgv : g v = 0 := by
      have h2 := hTapply v (Φ.symm g)
      rw [Φ.apply_symm_apply] at h2
      rw [← h2, show T v = 0 from hv]; rfl
    simp [hgv]
  have hTsurj : Function.Surjective
      (T : W →ₗ[𝕜] StrongDual 𝕜 (EuclideanSpace 𝕜 (Fin k))) := by
    have hrank : Module.finrank 𝕜 (LinearMap.range
        (T : W →ₗ[𝕜] StrongDual 𝕜 (EuclideanSpace 𝕜 (Fin k))))
        = Module.finrank 𝕜 (StrongDual 𝕜 (EuclideanSpace 𝕜 (Fin k))) := by
      rw [LinearMap.finrank_range_of_inj hTinj, hkSD, hkW]
    rw [← LinearMap.range_eq_top]
    exact Submodule.eq_top_of_finrank_eq hrank
  obtain ⟨w, hw⟩ := hTsurj (InnerProductSpace.toDual 𝕜 (EuclideanSpace 𝕜 (Fin k)) u₀)
  have hweval : ∀ g : StrongDual 𝕜 W, g w = ⟪u₀, Φ.symm g⟫_𝕜 := fun g => by
    have h1 : T w (Φ.symm g) = ⟪u₀, Φ.symm g⟫_𝕜 := by
      rw [show T w = InnerProductSpace.toDual 𝕜 (EuclideanSpace 𝕜 (Fin k)) u₀ from hw,
        InnerProductSpace.toDual_apply_apply]
    rwa [hTapply w (Φ.symm g), Φ.apply_symm_apply] at h1
  refine ⟨w, hweval, ?_⟩
  refine NormedSpace.norm_le_dual_bound 𝕜 w zero_le_one fun g => ?_
  rw [one_mul, hweval g]
  calc ‖⟪u₀, Φ.symm g⟫_𝕜‖ = ‖⟪Φ.symm g, u₀⟫_𝕜‖ := by
        rw [← inner_conj_symm (Φ.symm g) u₀, RCLike.norm_conj]
    _ ≤ q (Φ.symm g) := hu₀ (Φ.symm g)
    _ = ‖Φ (Φ.symm g)‖ := (hqΦ (Φ.symm g)).symm
    _ = ‖g‖ := by rw [Φ.apply_symm_apply]
private lemma sum_weight_smul_witness_eq
    (Φ : EuclideanSpace 𝕜 (Fin k) ≃L[𝕜] StrongDual 𝕜 W) (hΦ : ∀ z, ‖Φ z‖ ≤ ‖z‖)
    {N : ℕ} (c : Fin N → ℝ) (u : Fin N → EuclideanSpace 𝕜 (Fin k)) (w : Fin N → W)
    (hdec : ∀ z, ∑ i, ((c i : 𝕜) * ⟪u i, z⟫_𝕜) • u i = z)
    (hweval : ∀ i (g : StrongDual 𝕜 W), g (w i) = ⟪u i, Φ.symm g⟫_𝕜) (v : W) :
    (∑ i, ((c i : 𝕜) * (Φ (u i)) v) • w i) = v := by
  obtain ⟨r, hr, -⟩ := exists_riesz_repr Φ hΦ v
  apply (NormedSpace.inclusionInDoubleDualLi (E := W) 𝕜).injective
  apply ContinuousLinearMap.ext
  intro g
  have hLHS : (NormedSpace.inclusionInDoubleDualLi (E := W) 𝕜)
      (∑ i, ((c i : 𝕜) * (Φ (u i)) v) • w i) g
      = ∑ i, ((c i : 𝕜) * (Φ (u i)) v) * g (w i) := by
    show g (∑ i, ((c i : 𝕜) * (Φ (u i)) v) • w i) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
  have hRHS : (NormedSpace.inclusionInDoubleDualLi (E := W) 𝕜) v g = g v := rfl
  rw [hLHS, hRHS]
  -- Rewrite through the Riesz vector and the decomposition of identity.
  set z := Φ.symm g with hz
  have hgz : g = Φ z := by rw [hz, Φ.apply_symm_apply]
  calc ∑ i, ((c i : 𝕜) * (Φ (u i)) v) * g (w i)
      = ∑ i, (c i : 𝕜) * ⟪u i, z⟫_𝕜 * ⟪r, u i⟫_𝕜 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hweval i g, ← hz, hr (u i)]; ring
    _ = ⟪r, ∑ i, ((c i : 𝕜) * ⟪u i, z⟫_𝕜) • u i⟫_𝕜 := by
        rw [inner_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [inner_smul_right]
    _ = ⟪r, z⟫_𝕜 := by rw [hdec z]
    _ = (Φ z) v := hr z
    _ = g v := by rw [← hgz]
end DualProjection
end John
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped InnerProductSpace ComplexConjugate
open RCLike (re)
open John
variable {𝕜 : Type u} [RCLike 𝕜] {k : ℕ}
namespace John
theorem _root_.solution {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (M : Submodule 𝕜 X) [IsClosed (M : Set X)] [FiniteDimensional 𝕜 (X ⧸ M)]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : X →L[𝕜] X, P.comp P = P ∧ LinearMap.ker (P : X →ₗ[𝕜] X) = M ∧
      ‖P‖ ≤ Real.sqrt (Module.finrank 𝕜 (X ⧸ M)) + ε := by
  classical
  set k := Module.finrank 𝕜 (X ⧸ M) with hk
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- `codim M = 0`: the quotient is trivial, `M = ⊤`, and `P = 0` works.
    have hsub : Subsingleton (X ⧸ M) :=
      Module.finrank_zero_iff.mp (hk.symm.trans hk0)
    have hM : M = ⊤ := by
      ext x0
      simp only [Submodule.mem_top, iff_true]
      have := Subsingleton.elim (Submodule.Quotient.mk x0 : X ⧸ M) 0
      exact (Submodule.Quotient.mk_eq_zero M).mp this
    refine ⟨0, by simp, ?_, ?_⟩
    · rw [hM]; simp [LinearMap.ker_zero]
    · simp only [norm_zero]; positivity
  -- From now on `0 < k`. The finite-dimensional dual `D := (X ⧸ M)*`.
  have hEfin : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin k)) = k := finrank_euclideanSpace_fin
  have hDfin : FiniteDimensional 𝕜 (StrongDual 𝕜 (X ⧸ M)) :=
    Module.Finite.equiv
      (LinearMap.toContinuousLinearMap : ((X ⧸ M) →ₗ[𝕜] 𝕜) ≃ₗ[𝕜] ((X ⧸ M) →L[𝕜] 𝕜))
  have hkD : Module.finrank 𝕜 (StrongDual 𝕜 (X ⧸ M)) = k := by
    rw [← (LinearMap.toContinuousLinearMap :
          ((X ⧸ M) →ₗ[𝕜] 𝕜) ≃ₗ[𝕜] ((X ⧸ M) →L[𝕜] 𝕜)).finrank_eq]
    exact (Subspace.dual_finrank_eq (K := 𝕜) (V := X ⧸ M)).trans hk.symm
  -- A continuous linear equivalence `𝕜^k ≃L D`, and the John position along it:
  -- `Φ = L ∘ T₀` with `‖Φ z‖ = q z`.
  obtain ⟨Φ, q, hqc, hq1, hqmax, hqΦ⟩ :=
    exists_johnPosition hkpos (ContinuousLinearEquiv.ofFinrankEq (hEfin.trans hkD.symm) :
      EuclideanSpace 𝕜 (Fin k) ≃L[𝕜] StrongDual 𝕜 (X ⧸ M))
  -- The John decomposition of identity in John position.
  obtain ⟨N, u, c, hcontact, hcnn, hcsum, hdec⟩ := john_decomposition q hqc hq1 hqmax
  -- The John-position map is a contraction, so evaluation at `v ∈ X ⧸ M` pulls
  -- back through `Φ` to an inner product against a vector of norm `≤ ‖v‖`.
  have hΦle : ∀ z, ‖Φ z‖ ≤ ‖z‖ := fun z => (hqΦ z).trans_le (hq1 z)
  have hRiesz : ∀ v : X ⧸ M, ∃ r : EuclideanSpace 𝕜 (Fin k),
      (∀ z, ⟪r, z⟫_𝕜 = (Φ z) v) ∧ ‖r‖ ≤ ‖v‖ := fun v => exists_riesz_repr Φ hΦle v
  -- Represent each contact point `u i` by a vector `w i ∈ X ⧸ M` of norm `≤ 1`
  -- (`exists_witness_of_contact`, via the single dual `Φ.flip`).
  choose w hweval hwnorm using fun i =>
    exists_witness_of_contact hk.symm Φ hqΦ (u i) (norm_inner_le_of_contact (hcontact i))
  -- Lift each `w i` to a representative `x i ∈ X` with `‖x i‖ < 1 + ε'`; this is the
  -- sole source of the `ε`.
  set ε' : ℝ := ε / Real.sqrt k with hε'def
  have hsqrtk : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by exact_mod_cast hkpos)
  have hε' : 0 < ε' := div_pos hε hsqrtk
  choose x hxmk hxnorm using fun i => Submodule.Quotient.norm_mk_lt (w i) hε'
  have hxbound : ∀ i, ‖x i‖ ≤ 1 + ε' := fun i => by
    linarith [hxnorm i, hwnorm i]
  -- The projection `P = ∑ᵢ cᵢ · (Φ uᵢ)(π ·) · xᵢ`.
  set π : X →L[𝕜] X ⧸ M := M.mkQL with hπdef
  have hπmk : ∀ y : X, π y = Submodule.Quotient.mk y := fun y => by
    rw [hπdef, Submodule.mkQL_apply, Submodule.mkQ_apply]
  have hπx : ∀ i, π (x i) = w i := fun i => by rw [hπmk]; exact hxmk i
  have hπle : ∀ y : X, ‖π y‖ ≤ ‖y‖ := fun y => by
    rw [hπmk]; exact Submodule.Quotient.norm_mk_le M y
  set P : X →L[𝕜] X := ∑ i, (c i : 𝕜) • (((Φ (u i)).comp π).smulRight (x i)) with hP
  have hPapply : ∀ y, P y = ∑ i, ((c i : 𝕜) * (Φ (u i)) (π y)) • x i := fun y => by
    rw [hP]
    simp only [sum_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, smul_smul]
  -- Key identity: the weighted combination of the `w i` reproduces every `v`.
  have hkey : ∀ v : X ⧸ M, (∑ i, ((c i : 𝕜) * (Φ (u i)) v) • w i) = v :=
    fun v => sum_weight_smul_witness_eq Φ hΦle c u w hdec hweval v
  have hπP : ∀ y, π (P y) = π y := fun y => by
    have hsum : π (P y) = ∑ i, ((c i : 𝕜) * (Φ (u i)) (π y)) • w i := by
      rw [hPapply, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hπx i]
    rw [hsum, hkey (π y)]
  refine ⟨P, ?_, ?_, ?_⟩
  · -- `P ∘ P = P`, since `π ∘ P = π`.
    ext y
    show P (P y) = P y
    rw [hPapply (P y), hπP y, ← hPapply y]
  · -- `ker P = M`.
    ext x0
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    constructor
    · intro hPx
      have h0 : π x0 = 0 := by rw [← hπP x0, hPx, map_zero]
      rw [hπmk] at h0
      exact (Submodule.Quotient.mk_eq_zero M).mp h0
    · intro hx0
      have h0 : π x0 = 0 := by rw [hπmk]; exact (Submodule.Quotient.mk_eq_zero M).mpr hx0
      rw [hPapply, h0]
      simp
  · -- `‖P‖ ≤ √k + ε`.
    have hbnd : (0 : ℝ) ≤ Real.sqrt k + ε := by positivity
    refine ContinuousLinearMap.opNorm_le_bound P hbnd fun y => ?_
    obtain ⟨r, hr, hrnorm⟩ := hRiesz (π y)
    -- `∑ᵢ cᵢ ‖fᵢ(πy)‖² = ‖r‖² ≤ ‖y‖²` via the quadratic identity.
    have hquad : ∑ i, c i * ‖(Φ (u i)) (π y)‖ ^ 2 ≤ ‖y‖ ^ 2 := by
      have h1 : ∀ i, ‖(Φ (u i)) (π y)‖ = ‖⟪u i, r⟫_𝕜‖ := fun i => by
        rw [← hr (u i), ← inner_conj_symm r (u i), RCLike.norm_conj]
      calc ∑ i, c i * ‖(Φ (u i)) (π y)‖ ^ 2
          = ∑ i, c i * ‖⟪u i, r⟫_𝕜‖ ^ 2 := by
            exact Finset.sum_congr rfl fun i _ => by rw [h1 i]
        _ = ‖r‖ ^ 2 := sum_weight_inner_sq c u hdec r
        _ ≤ ‖π y‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg r) hrnorm 2
        _ ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hπle y) 2
    -- Cauchy–Schwarz: `∑ᵢ cᵢ ‖fᵢ(πy)‖ ≤ √k · ‖y‖`.
    have hCS : ∑ i, c i * ‖(Φ (u i)) (π y)‖ ≤ Real.sqrt k * ‖y‖ := by
      calc ∑ i, c i * ‖(Φ (u i)) (π y)‖
          ≤ Real.sqrt (∑ i, c i) * Real.sqrt (∑ i, c i * ‖(Φ (u i)) (π y)‖ ^ 2) :=
            sum_weight_mul_le_sqrt c hcnn _
        _ ≤ Real.sqrt k * Real.sqrt (‖y‖ ^ 2) := by
            rw [hcsum]
            exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hquad) (Real.sqrt_nonneg _)
        _ = Real.sqrt k * ‖y‖ := by rw [Real.sqrt_sq (norm_nonneg _)]
    -- Assemble.
    calc ‖P y‖ ≤ ∑ i, ‖((c i : 𝕜) * (Φ (u i)) (π y)) • x i‖ := by
          rw [hPapply]; exact norm_sum_le _ _
      _ = ∑ i, c i * ‖(Φ (u i)) (π y)‖ * ‖x i‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_smul, norm_mul, RCLike.norm_ofReal, abs_of_nonneg (hcnn i)]
      _ ≤ ∑ i, c i * ‖(Φ (u i)) (π y)‖ * (1 + ε') := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul_of_nonneg_left (hxbound i)
            (mul_nonneg (hcnn i) (norm_nonneg _))
      _ = (1 + ε') * ∑ i, c i * ‖(Φ (u i)) (π y)‖ := by
          rw [← Finset.sum_mul, mul_comm]
      _ ≤ (1 + ε') * (Real.sqrt k * ‖y‖) :=
          mul_le_mul_of_nonneg_left hCS (by positivity)
      _ = (Real.sqrt k + ε) * ‖y‖ := by
          rw [← mul_assoc, show (1 + ε') * Real.sqrt k = Real.sqrt k + ε from by
            rw [hε'def, add_mul, one_mul, div_mul_cancel₀ ε (ne_of_gt hsqrtk)]]
end John
