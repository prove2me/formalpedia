-- Prove2me | solution 1 for NoLocalBroadcast.Broadcast.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-08T05:48:57.669332+00:00
-- url     : https://prove2.me/submissions/83043416-04c5-4aec-8e3d-7e2ebf338bac

import Mathlib
import Definitions.Def_NoLocalBroadcast_Broadcast_Model

set_option autoImplicit false

namespace P412

open Matrix
open scoped Kronecker ComplexOrder

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- PSD matrices factor as `Bᴴ * B`. -/
lemma psd_factor {n : Type} [Fintype n] [DecidableEq n] (ω : Matrix n n ℂ)
    (h : ω.PosSemidef) : ∃ B : Matrix n n ℂ, ω = Bᴴ * B := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h.nonneg
  exact ⟨B, by rw [hB]; rfl⟩

/-- Duality of the Kraus map with its Heisenberg dual under the trace. -/
lemma trace_mul_dual {a : Type} [Fintype a] [DecidableEq a] {m : ℕ} (A : Fin m → Matrix a a ℂ)
    (ω Y : Matrix a a ℂ) :
    (ω * ∑ j, (A j)ᴴ * Y * A j).trace = (QAlgorithms.krausApply A ω * Y).trace := by
  simp only [QAlgorithms.krausApply, Finset.mul_sum, Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc]

/-- C1 (trace trick). -/
theorem C1 {a : Type} [Fintype a] [DecidableEq a] {m : ℕ} (A : Fin m → Matrix a a ℂ)
    (ω Z : Matrix a a ℂ) (hK : QAlgorithms.IsKrausFamily A) (hω : ω.PosSemidef)
    (hfix : QAlgorithms.krausApply A ω = ω)
    (hZ : (∑ j, (A j)ᴴ * Z * A j) = Z) : ∀ j, (Z * A j - A j * Z) * ω = 0 := by
  have hK' : (∑ j, (A j)ᴴ * A j) = 1 := hK
  have hZH : (∑ j, (A j)ᴴ * Zᴴ * A j) = Zᴴ := by
    have := congrArg Matrix.conjTranspose hZ
    simpa [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, Matrix.mul_assoc] using this
  have e : ∀ j, (Z * A j - A j * Z)ᴴ * (Z * A j - A j * Z) =
      (A j)ᴴ * (Zᴴ * Z) * A j - ((A j)ᴴ * Zᴴ * A j) * Z - Zᴴ * ((A j)ᴴ * Z * A j)
        + Zᴴ * ((A j)ᴴ * A j) * Z := by
    intro j
    simp only [conjTranspose_sub, conjTranspose_mul]
    noncomm_ring
  have key : (∑ j, (Z * A j - A j * Z)ᴴ * (Z * A j - A j * Z)) =
      (∑ j, (A j)ᴴ * (Zᴴ * Z) * A j) - Zᴴ * Z := by
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hZH, ← Finset.mul_sum, hZ, ← Finset.sum_mul, ← Finset.mul_sum, hK']
    noncomm_ring
  obtain ⟨B, rfl⟩ := psd_factor ω hω
  -- the traces `Tr(Bᴴ B Cᴴ C) = Tr((C Bᴴ)ᴴ (C Bᴴ))` sum to zero
  have hsum : (∑ j, ((Z * A j - A j * Z) * Bᴴ)ᴴ * ((Z * A j - A j * Z) * Bᴴ)).trace = 0 := by
    have h1 : ∀ j, (((Z * A j - A j * Z) * Bᴴ)ᴴ * ((Z * A j - A j * Z) * Bᴴ)).trace =
        (Bᴴ * B * ((Z * A j - A j * Z)ᴴ * (Z * A j - A j * Z))).trace := by
      intro j
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm Bᴴ]
      simp only [Matrix.mul_assoc]
    rw [Matrix.trace_sum, Finset.sum_congr rfl (fun j _ => h1 j), ← Matrix.trace_sum,
      ← Finset.mul_sum, key, Matrix.mul_sub, Matrix.trace_sub, trace_mul_dual, hfix, sub_self]
  rw [Matrix.trace_sum] at hsum
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ (((Z * A j - A j * Z) * Bᴴ)ᴴ *
      ((Z * A j - A j * Z) * Bᴴ)).trace :=
    fun j _ => (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum
  intro j
  have := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (hz j (Finset.mem_univ _))
  rw [← Matrix.mul_assoc, this, Matrix.zero_mul]

/-- C2 (multiplicative domain). -/
theorem C2 {a : Type} [Fintype a] [DecidableEq a] {m : ℕ} (K : Fin m → Matrix (a × a) a ℂ)
    (Z W : Matrix a a ℂ) (hK : QAlgorithms.IsKrausFamily K)
    (hZ : ∀ k, K k * Z = (Z ⊗ₖ (1 : Matrix a a ℂ)) * K k)
    (hW : ∀ k, K k * W = ((1 : Matrix a a ℂ) ⊗ₖ W) * K k) : Z * W = W * Z := by
  have hK' : (∑ k, (K k)ᴴ * K k) = 1 := hK
  have hc : (Z ⊗ₖ (1 : Matrix a a ℂ)) * ((1 : Matrix a a ℂ) ⊗ₖ W) =
      ((1 : Matrix a a ℂ) ⊗ₖ W) * (Z ⊗ₖ (1 : Matrix a a ℂ)) := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp
  have h1 : Z * W = ∑ k, (K k)ᴴ * ((Z ⊗ₖ (1 : Matrix a a ℂ)) * ((1 : Matrix a a ℂ) ⊗ₖ W)) * K k := by
    have : ∀ k, (K k)ᴴ * ((Z ⊗ₖ (1 : Matrix a a ℂ)) * ((1 : Matrix a a ℂ) ⊗ₖ W)) * K k =
        (K k)ᴴ * K k * (Z * W) := by
      intro k
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← hW, ← Matrix.mul_assoc _ (K k), ← hZ]
      simp only [Matrix.mul_assoc]
    rw [Finset.sum_congr rfl (fun k _ => this k), ← Finset.sum_mul, hK', Matrix.one_mul]
  have h2 : W * Z = ∑ k, (K k)ᴴ * (((1 : Matrix a a ℂ) ⊗ₖ W) * (Z ⊗ₖ (1 : Matrix a a ℂ))) * K k := by
    have : ∀ k, (K k)ᴴ * (((1 : Matrix a a ℂ) ⊗ₖ W) * (Z ⊗ₖ (1 : Matrix a a ℂ))) * K k =
        (K k)ᴴ * K k * (W * Z) := by
      intro k
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← hZ, ← Matrix.mul_assoc _ (K k), ← hW]
      simp only [Matrix.mul_assoc]
    rw [Finset.sum_congr rfl (fun k _ => this k), ← Finset.sum_mul, hK', Matrix.one_mul]
  rw [h1, h2, hc]

/-- C3a: a commuting set of Hermitian matrices has a joint orthonormal eigenbasis. -/
theorem joint_eigenbasis {a : Type} [Fintype a] [DecidableEq a] (S : Set (Matrix a a ℂ))
    (hH : ∀ X ∈ S, X.IsHermitian) (hc : ∀ X ∈ S, ∀ Y ∈ S, X * Y = Y * X) :
    ∃ e : OrthonormalBasis (Fin (Fintype.card a)) ℂ (EuclideanSpace ℂ a),
      ∀ X ∈ S, ∀ i, ∃ c : ℂ, Matrix.toEuclideanLin X (e i) = c • e i := by
  classical
  let T : S → Module.End ℂ (EuclideanSpace ℂ a) := fun X => Matrix.toEuclideanLin X.1
  have hT : ∀ i, (T i).IsSymmetric := fun X =>
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (hH X.1 X.2)
  have hC : Pairwise (fun X Y => Commute (T X) (T Y)) := by
    intro X Y _
    show Matrix.toEuclideanLin X.1 * Matrix.toEuclideanLin Y.1 =
      Matrix.toEuclideanLin Y.1 * Matrix.toEuclideanLin X.1
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp]
    have h := congrArg (fun M => (Matrix.toEuclideanLin M : Module.End ℂ (EuclideanSpace ℂ a)))
      (hc X.1 X.2 Y.1 Y.2)
    simpa only [Matrix.toLpLin_mul_same] using h
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT hC
  have hO := LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hT
  let W : (S → ℂ) → Submodule ℂ (EuclideanSpace ℂ a) :=
    fun χ => ⨅ j, Module.End.eigenspace (T j) (χ j)
  let _ : Fintype {χ // W χ ≠ ⊥} := hO.independent.fintypeNeBotOfFiniteDimensional
  let V : {χ // W χ ≠ ⊥} → Submodule ℂ (EuclideanSpace ℂ a) := fun χ => W χ.1
  have hO' : OrthogonalFamily ℂ (fun i => V i) fun i => (V i).subtypeₗᵢ :=
    hO.comp Subtype.val_injective
  have hI' : DirectSum.IsInternal V := by
    rw [hO'.isInternal_iff]
    have : (⨆ i, V i) = ⊤ := by
      simp only [V]
      rw [iSup_ne_bot_subtype W]
      exact htop
    rw [this, Submodule.top_orthogonal_eq_bot]
  have hn : Module.finrank ℂ (EuclideanSpace ℂ a) = Fintype.card a := finrank_euclideanSpace
  refine ⟨hI'.subordinateOrthonormalBasis hn hO', fun X hX i => ?_⟩
  have hmem := hI'.subordinateOrthonormalBasis_subordinate hn i hO'
  refine ⟨(hI'.subordinateOrthonormalBasisIndex hn i hO').1 ⟨X, hX⟩, ?_⟩
  have h2 := (Submodule.mem_iInf _).mp hmem ⟨X, hX⟩
  exact Module.End.mem_eigenspace_iff.mp h2

lemma one_kron_mul_apply {a b : Type} [Fintype a] [DecidableEq a] [Fintype b]
    (ρ : Matrix (a × b) (a × b) ℂ) (Y : Matrix b b ℂ) (k j : a) (h h' : b) :
    (((1 : Matrix a a ℂ) ⊗ₖ Y) * ρ) (k, h) (j, h') = ∑ y, Y h y * ρ (k, y) (j, h') := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, ite_mul, Finset.sum_ite_eq]

/-- C3b: slices of a Hermitian state by Hermitian `Y` are Hermitian. -/
theorem slice_isHermitian {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : ρ.IsHermitian) (Y : Matrix b b ℂ) (hY : Y.IsHermitian) :
    (QAlgorithms.traceRight (((1 : Matrix a a ℂ) ⊗ₖ Y) * ρ)).IsHermitian := by
  have hρ' : ∀ x y, star (ρ y x) = ρ x y := fun x y => by
    have := congrFun (congrFun hρ x) y
    simpa [Matrix.conjTranspose_apply] using this
  have hY' : ∀ x y, star (Y y x) = Y x y := fun x y => by
    have := congrFun (congrFun hY x) y
    simpa [Matrix.conjTranspose_apply] using this
  ext j k
  simp only [Matrix.conjTranspose_apply, QAlgorithms.traceRight, Matrix.of_apply,
    one_kron_mul_apply, star_sum, star_mul', hρ', hY']
  rw [Finset.sum_comm]

/-! ### C3 (c-e): commuting slices on both sides give a classical-classical state -/

/-- Outer product `|u⟩⟨v|`. -/
noncomputable def outer {ι : Type} (u v : EuclideanSpace ℂ ι) : Matrix ι ι ℂ :=
  Matrix.of fun x y => u x * starRingEnd ℂ (v y)

/-- Matrix element `⟨u ⊗ v| ρ |u' ⊗ v'⟩`. -/
noncomputable def melt {a b : Type} [Fintype a] [Fintype b] (ρ : Matrix (a × b) (a × b) ℂ)
    (u : EuclideanSpace ℂ a) (v : EuclideanSpace ℂ b) (u' : EuclideanSpace ℂ a)
    (v' : EuclideanSpace ℂ b) : ℂ :=
  ∑ p : a × b, ∑ q : a × b, starRingEnd ℂ (u p.1 * v p.2) * ρ p q * (u' q.1 * v' q.2)

lemma kron_one_mul_apply {a b : Type} [Fintype a] [Fintype b] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ) (X : Matrix a a ℂ) (k j : a) (h h' : b) :
    ((X ⊗ₖ (1 : Matrix b b ℂ)) * ρ) (k, h) (j, h') = ∑ x, X k x * ρ (x, h) (j, h') := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, mul_ite, ite_mul,
    Finset.sum_ite_eq]

/-- C3c: B-side slices of a Hermitian state by Hermitian `X` are Hermitian. -/
theorem sliceB_isHermitian {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : ρ.IsHermitian) (X : Matrix a a ℂ) (hX : X.IsHermitian) :
    (QAlgorithms.traceLeft ((X ⊗ₖ (1 : Matrix b b ℂ)) * ρ)).IsHermitian := by
  have hρ' : ∀ x y, star (ρ y x) = ρ x y := fun x y => by
    have := congrFun (congrFun hρ x) y
    simpa [Matrix.conjTranspose_apply] using this
  have hX' : ∀ x y, star (X y x) = X x y := fun x y => by
    have := congrFun (congrFun hX x) y
    simpa [Matrix.conjTranspose_apply] using this
  ext j k
  simp only [Matrix.conjTranspose_apply, QAlgorithms.traceLeft, Matrix.of_apply,
    kron_one_mul_apply, star_sum, star_mul', hρ', hX']
  rw [Finset.sum_comm]

lemma sliceA_add_smul {a b : Type} [Fintype a] [DecidableEq a] [Fintype b]
    (ρ : Matrix (a × b) (a × b) ℂ) (Y₁ Y₂ : Matrix b b ℂ) (c : ℂ) :
    QAlgorithms.traceRight (((1 : Matrix a a ℂ) ⊗ₖ (Y₁ + c • Y₂)) * ρ) =
      QAlgorithms.traceRight (((1 : Matrix a a ℂ) ⊗ₖ Y₁) * ρ) +
        c • QAlgorithms.traceRight (((1 : Matrix a a ℂ) ⊗ₖ Y₂) * ρ) := by
  ext j k
  simp only [QAlgorithms.traceRight, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
    one_kron_mul_apply, add_mul, Finset.sum_add_distrib, smul_eq_mul, Finset.mul_sum, mul_assoc]

lemma sliceB_add_smul {a b : Type} [Fintype a] [Fintype b] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ) (X₁ X₂ : Matrix a a ℂ) (c : ℂ) :
    QAlgorithms.traceLeft (((X₁ + c • X₂) ⊗ₖ (1 : Matrix b b ℂ)) * ρ) =
      QAlgorithms.traceLeft ((X₁ ⊗ₖ (1 : Matrix b b ℂ)) * ρ) +
        c • QAlgorithms.traceLeft ((X₂ ⊗ₖ (1 : Matrix b b ℂ)) * ρ) := by
  ext j k
  simp only [QAlgorithms.traceLeft, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
    kron_one_mul_apply, add_mul, Finset.sum_add_distrib, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- Every square matrix is `H₁ + i H₂` with `H₁, H₂` Hermitian. -/
lemma herm_decomp {n : Type} (Y : Matrix n n ℂ) :
    ∃ H₁ H₂ : Matrix n n ℂ, H₁.IsHermitian ∧ H₂.IsHermitian ∧ Y = H₁ + Complex.I • H₂ := by
  refine ⟨(1 / 2 : ℂ) • (Y + Yᴴ), (-Complex.I / 2) • (Y - Yᴴ), ?_, ?_, ?_⟩
  · simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose]
    rw [add_comm Yᴴ Y]; congr 1; simp
  · simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose]
    rw [← neg_sub Y Yᴴ, smul_neg, ← neg_smul]; congr 1
    simp [Complex.ext_iff]
    try norm_num
  · ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring_nf
    simp [Complex.I_sq]
    ring

/-- Matrix elements in an eigenbasis: an off-diagonal element of `X` vanishes when `e k` is an
eigenvector of `X`. -/
lemma offdiag_zero_of_eigen {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (e : OrthonormalBasis κ ℂ (EuclideanSpace ℂ ι)) (X : Matrix ι ι ℂ) (k : κ) (c : ℂ)
    (h : Matrix.toEuclideanLin X (e k) = c • e k) (i : κ) (hik : i ≠ k) :
    ∑ x, ∑ x', starRingEnd ℂ (e i x) * X x x' * e k x' = 0 := by
  have h2 : ∀ x, ∑ x', X x x' * e k x' = c * e k x := fun x => by
    have := congrArg (fun v : EuclideanSpace ℂ ι => v x) h
    simpa [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct] using this
  have h3 : ∑ x, starRingEnd ℂ (e i x) * e k x = 0 := by
    have := e.orthonormal.2 hik
    simpa [PiLp.inner_apply, RCLike.inner_apply, mul_comm] using this
  calc _ = ∑ x, starRingEnd ℂ (e i x) * ∑ x', X x x' * e k x' := by
        simp [Finset.mul_sum, mul_assoc]
    _ = c * ∑ x, starRingEnd ℂ (e i x) * e k x := by
        simp only [h2, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
    _ = 0 := by rw [h3, mul_zero]

/-- A-side slice by `|v'⟩⟨v|` has matrix elements `⟨u ⊗ v|ρ|u' ⊗ v'⟩`. -/
lemma sliceA_entry {a b : Type} [Fintype a] [DecidableEq a] [Fintype b]
    (ρ : Matrix (a × b) (a × b) ℂ) (u u' : EuclideanSpace ℂ a) (v v' : EuclideanSpace ℂ b) :
    ∑ x, ∑ x', starRingEnd ℂ (u x) *
        QAlgorithms.traceRight (((1 : Matrix a a ℂ) ⊗ₖ outer v' v) * ρ) x x' * u' x' =
      melt ρ u v u' v' := by
  simp only [QAlgorithms.traceRight, Matrix.of_apply, one_kron_mul_apply, outer, melt,
    Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, map_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => by ring

/-- B-side slice by `|u'⟩⟨u|` has matrix elements `⟨u ⊗ v|ρ|u' ⊗ v'⟩`. -/
lemma sliceB_entry {a b : Type} [Fintype a] [Fintype b] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ) (u u' : EuclideanSpace ℂ a) (v v' : EuclideanSpace ℂ b) :
    ∑ y, ∑ y', starRingEnd ℂ (v y) *
        QAlgorithms.traceLeft ((outer u' u ⊗ₖ (1 : Matrix b b ℂ)) * ρ) y y' * v' y' =
      melt ρ u v u' v' := by
  simp only [QAlgorithms.traceLeft, Matrix.of_apply, kron_one_mul_apply, outer, melt,
    Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, map_mul]
  conv_lhs => enter [2, y]; rw [Finset.sum_comm]
  conv_lhs => enter [2, y, 2, x]; rw [Finset.sum_comm]
  conv_lhs => enter [2, y]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma sum_outer_self {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (e : OrthonormalBasis κ ℂ (EuclideanSpace ℂ ι)) : ∑ i, outer (e i) (e i) = 1 := by
  ext x x'
  have h := congrArg (fun v : EuclideanSpace ℂ ι => v x)
    (e.sum_repr' (EuclideanSpace.single x' (1 : ℂ)))
  simp only [EuclideanSpace.inner_single_right, mul_one] at h
  rw [Matrix.sum_apply]
  simp only [outer, Matrix.of_apply, Matrix.one_apply]
  simpa [EuclideanSpace.single_apply, mul_comm, eq_comm] using h

lemma sum_kron {ι α β γ δ : Type} [Fintype ι] (A : ι → Matrix α β ℂ) (B : Matrix γ δ ℂ) :
    (∑ i, A i) ⊗ₖ B = ∑ i, A i ⊗ₖ B := by
  ext p q
  simp [Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul]

lemma kron_sum {ι α β γ δ : Type} [Fintype ι] (A : Matrix α β ℂ) (B : ι → Matrix γ δ ℂ) :
    A ⊗ₖ (∑ i, B i) = ∑ i, A ⊗ₖ B i := by
  ext p q
  simp [Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.mul_sum]

lemma sandwich {a b : Type} [Fintype a] [Fintype b] (ρ : Matrix (a × b) (a × b) ℂ)
    (u u' : EuclideanSpace ℂ a) (v v' : EuclideanSpace ℂ b) :
    (outer u u ⊗ₖ outer v v) * ρ * (outer u' u' ⊗ₖ outer v' v') =
      melt ρ u v u' v' • (outer u u' ⊗ₖ outer v v') := by
  ext p q
  simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, outer, Matrix.of_apply, melt,
    Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, map_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by ring

lemma melt_self_eq_dot {a b : Type} [Fintype a] [Fintype b] (ρ : Matrix (a × b) (a × b) ℂ)
    (u : EuclideanSpace ℂ a) (v : EuclideanSpace ℂ b) :
    melt ρ u v u v = star (fun p : a × b => u p.1 * v p.2) ⬝ᵥ
      (ρ *ᵥ fun p : a × b => u p.1 * v p.2) := by
  simp only [melt, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
  rfl

lemma trace_outer_self {ι : Type} [Fintype ι] (u : EuclideanSpace ℂ ι) :
    (outer u u).trace = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq]
  push_cast
  simp only [Matrix.trace, Matrix.diag, outer, Matrix.of_apply, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  push_cast
  rfl

set_option maxHeartbeats 1000000 in
/-- C3: commuting slices on both sides give a classical-classical state. -/
theorem C3 {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ)
    (hA : ∀ Y Y' : Matrix b b ℂ,
      QAlgorithms.traceRight (((1 : Matrix a a ℂ) ⊗ₖ Y) * ρ) *
          QAlgorithms.traceRight (((1 : Matrix a a ℂ) ⊗ₖ Y') * ρ) =
        QAlgorithms.traceRight (((1 : Matrix a a ℂ) ⊗ₖ Y') * ρ) *
          QAlgorithms.traceRight (((1 : Matrix a a ℂ) ⊗ₖ Y) * ρ))
    (hB : ∀ X X' : Matrix a a ℂ,
      QAlgorithms.traceLeft ((X ⊗ₖ (1 : Matrix b b ℂ)) * ρ) *
          QAlgorithms.traceLeft ((X' ⊗ₖ (1 : Matrix b b ℂ)) * ρ) =
        QAlgorithms.traceLeft ((X' ⊗ₖ (1 : Matrix b b ℂ)) * ρ) *
          QAlgorithms.traceLeft ((X ⊗ₖ (1 : Matrix b b ℂ)) * ρ)) :
    NoLocalBroadcast.Broadcast.IsClassicalClassical ρ := by
  have hH : ρ.IsHermitian := hρ.1.isHermitian
  obtain ⟨e, he⟩ := joint_eigenbasis
    {X | ∃ Y : Matrix b b ℂ, Y.IsHermitian ∧ X = QAlgorithms.traceRight (((1 : Matrix a a ℂ) ⊗ₖ Y) * ρ)}
    (by rintro X ⟨Y, hY, rfl⟩; exact slice_isHermitian ρ hH Y hY)
    (by rintro X ⟨Y, -, rfl⟩ X' ⟨Y', -, rfl⟩; exact hA Y Y')
  obtain ⟨f, hf⟩ := joint_eigenbasis
    {X | ∃ Y : Matrix a a ℂ, Y.IsHermitian ∧ X = QAlgorithms.traceLeft ((Y ⊗ₖ (1 : Matrix b b ℂ)) * ρ)}
    (by rintro X ⟨Y, hY, rfl⟩; exact sliceB_isHermitian ρ hH Y hY)
    (by rintro X ⟨Y, -, rfl⟩ X' ⟨Y', -, rfl⟩; exact hB Y Y')
  have hoffA : ∀ i k, i ≠ k → ∀ j l, melt ρ (e i) (f j) (e k) (f l) = 0 := by
    intro i k hik j l
    rw [← sliceA_entry]
    obtain ⟨H₁, H₂, h₁, h₂, hY⟩ := herm_decomp (outer (f l) (f j))
    obtain ⟨c₁, hc₁⟩ := he _ ⟨H₁, h₁, rfl⟩ k
    obtain ⟨c₂, hc₂⟩ := he _ ⟨H₂, h₂, rfl⟩ k
    apply offdiag_zero_of_eigen e _ k (c₁ + Complex.I * c₂) _ i hik
    rw [hY, sliceA_add_smul, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      hc₁, hc₂, smul_smul, ← add_smul]
  have hoffB : ∀ j l, j ≠ l → ∀ i k, melt ρ (e i) (f j) (e k) (f l) = 0 := by
    intro j l hjl i k
    rw [← sliceB_entry]
    obtain ⟨H₁, H₂, h₁, h₂, hY⟩ := herm_decomp (outer (e k) (e i))
    obtain ⟨c₁, hc₁⟩ := hf _ ⟨H₁, h₁, rfl⟩ l
    obtain ⟨c₂, hc₂⟩ := hf _ ⟨H₂, h₂, rfl⟩ l
    apply offdiag_zero_of_eigen f _ l (c₁ + Complex.I * c₂) _ j hjl
    rw [hY, sliceB_add_smul, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      hc₁, hc₂, smul_smul, ← add_smul]
  have hnn : ∀ i j, 0 ≤ melt ρ (e i) (f j) (e i) (f j) := fun i j => by
    rw [melt_self_eq_dot]
    exact hρ.1.dotProduct_mulVec_nonneg _
  have hreal : ∀ i j, ((melt ρ (e i) (f j) (e i) (f j)).re : ℂ) = melt ρ (e i) (f j) (e i) (f j) :=
    fun i j => by
      have h := Complex.le_def.mp (hnn i j)
      apply Complex.ext <;> simp [← h.2]
  have hrec : ρ = ∑ ij : Fin (Fintype.card a) × Fin (Fintype.card b),
      (((melt ρ (e ij.1) (f ij.2) (e ij.1) (f ij.2)).re : ℝ) : ℂ) •
        (QAlgorithms.pureDensity (e ij.1) ⊗ₖ QAlgorithms.pureDensity (f ij.2)) := by
    calc ρ = ((∑ i, outer (e i) (e i)) ⊗ₖ (∑ j, outer (f j) (f j))) * ρ *
          ((∑ k, outer (e k) (e k)) ⊗ₖ (∑ l, outer (f l) (f l))) := by
          rw [sum_outer_self e, sum_outer_self f, Matrix.one_kronecker_one, Matrix.one_mul,
            Matrix.mul_one]
      _ = ∑ l, ∑ k, ∑ j, ∑ i, melt ρ (e i) (f j) (e k) (f l) •
            (outer (e i) (e k) ⊗ₖ outer (f j) (f l)) := by
          simp only [sum_kron, kron_sum, Finset.sum_mul, Finset.mul_sum, sandwich]
      _ = ∑ l, ∑ k, melt ρ (e k) (f l) (e k) (f l) • (outer (e k) (e k) ⊗ₖ outer (f l) (f l)) := by
          refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
          rw [Fintype.sum_eq_single l fun j hj =>
            Finset.sum_eq_zero fun i _ => by rw [hoffB j l hj i k, zero_smul]]
          rw [Fintype.sum_eq_single k fun i hi => by rw [hoffA i k hi l l, zero_smul]]
      _ = _ := by
          rw [Finset.sum_comm, Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [hreal]; rfl
  refine ⟨Fintype.card a, Fintype.card b, fun i => e i, fun j => f j,
    fun ij => (melt ρ (e ij.1) (f ij.2) (e ij.1) (f ij.2)).re, e.orthonormal, f.orthonormal,
    fun ij => (Complex.le_def.mp (hnn ij.1 ij.2)).1, ?_, hrec⟩
  have ht := congrArg Matrix.trace hrec
  have hone : ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
      (g : OrthonormalBasis κ ℂ (EuclideanSpace ℂ ι)) (i : κ),
      (QAlgorithms.pureDensity (g i)).trace = 1 := fun g i => by
    rw [show QAlgorithms.pureDensity (g i) = outer (g i) (g i) from rfl, trace_outer_self,
      g.orthonormal.1 i]
    simp
  rw [hρ.2, Matrix.trace_sum] at ht
  simp only [Matrix.trace_smul, Matrix.trace_kronecker, hone, mul_one, smul_eq_mul] at ht
  exact_mod_cast ht.symm

/-! ### C4core building blocks: Kadison–Schwarz defect for a Kraus family -/

/-- Kadison–Schwarz defect identity: with `Φ = ∑ Aᴴ Z' A`,
`∑ (Z' A - A Φ)ᴴ (Z' A - A Φ) = ∑ Aᴴ Z'ᴴ Z' A - Φᴴ Φ`. -/
lemma ks_defect {a c : Type} [Fintype a] [DecidableEq a] [Fintype c] {m : ℕ}
    (A : Fin m → Matrix c a ℂ) (hK : QAlgorithms.IsKrausFamily A) (Z' : Matrix c c ℂ) :
    ∑ j, (Z' * A j - A j * (∑ i, (A i)ᴴ * Z' * A i))ᴴ *
        (Z' * A j - A j * (∑ i, (A i)ᴴ * Z' * A i)) =
      (∑ j, (A j)ᴴ * (Z'ᴴ * Z') * A j) -
        (∑ i, (A i)ᴴ * Z' * A i)ᴴ * (∑ i, (A i)ᴴ * Z' * A i) := by
  have hK' : (∑ j, (A j)ᴴ * A j) = 1 := hK
  set Φ := ∑ i, (A i)ᴴ * Z' * A i with hΦ
  have hΦH : (∑ j, (A j)ᴴ * Z'ᴴ * A j) = Φᴴ := by
    rw [hΦ, Matrix.conjTranspose_sum]
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have e : ∀ j, (Z' * A j - A j * Φ)ᴴ * (Z' * A j - A j * Φ) =
      (A j)ᴴ * (Z'ᴴ * Z') * A j - ((A j)ᴴ * Z'ᴴ * A j) * Φ - Φᴴ * ((A j)ᴴ * Z' * A j)
        + Φᴴ * ((A j)ᴴ * A j) * Φ := by
    intro j
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.mul_assoc]
    abel
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, hΦH, ← Finset.mul_sum, ← hΦ, ← Finset.sum_mul, ← Finset.mul_sum, hK']
  noncomm_ring

/-- Weighted Kadison–Schwarz: if the `ω`-weighted defect vanishes, `Z'` intertwines the Kraus
operators with `Φ = ∑ Aᴴ Z' A` on the support of `ω`. -/
lemma intertwine_of_defect {a c : Type} [Fintype a] [DecidableEq a] [Fintype c] {m : ℕ}
    (A : Fin m → Matrix c a ℂ) (hK : QAlgorithms.IsKrausFamily A) (Z' : Matrix c c ℂ)
    (ω : Matrix a a ℂ) (hω : ω.PosSemidef)
    (hdef : (ω * ((∑ j, (A j)ᴴ * (Z'ᴴ * Z') * A j) -
        (∑ i, (A i)ᴴ * Z' * A i)ᴴ * (∑ i, (A i)ᴴ * Z' * A i))).trace = 0) :
    ∀ j, (Z' * A j - A j * (∑ i, (A i)ᴴ * Z' * A i)) * ω = 0 := by
  rw [← ks_defect A hK Z'] at hdef
  obtain ⟨B, rfl⟩ := psd_factor ω hω
  set C := fun j => Z' * A j - A j * (∑ i, (A i)ᴴ * Z' * A i) with hC
  have hsum : (∑ j, (C j * Bᴴ)ᴴ * (C j * Bᴴ)).trace = 0 := by
    have h1 : ∀ j, ((C j * Bᴴ)ᴴ * (C j * Bᴴ)).trace = (Bᴴ * B * ((C j)ᴴ * C j)).trace := by
      intro j
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm Bᴴ]
      simp only [Matrix.mul_assoc]
    rw [Matrix.trace_sum, Finset.sum_congr rfl (fun j _ => h1 j), ← Matrix.trace_sum,
      ← Finset.mul_sum]
    exact hdef
  rw [Matrix.trace_sum] at hsum
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ ((C j * Bᴴ)ᴴ * (C j * Bᴴ)).trace :=
    fun j _ => (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum
  intro j
  have := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (hz j (Finset.mem_univ _))
  show C j * (Bᴴ * B) = 0
  rw [← Matrix.mul_assoc, this, Matrix.zero_mul]

/-- The `ω`-weighted Kadison–Schwarz defect is nonnegative (`Φ` is an `L²(ω)` contraction). -/
lemma defect_nonneg {a c : Type} [Fintype a] [DecidableEq a] [Fintype c] {m : ℕ}
    (A : Fin m → Matrix c a ℂ) (hK : QAlgorithms.IsKrausFamily A) (Z' : Matrix c c ℂ)
    (ω : Matrix a a ℂ) (hω : ω.PosSemidef) :
    0 ≤ (ω * ((∑ j, (A j)ᴴ * (Z'ᴴ * Z') * A j) -
        (∑ i, (A i)ᴴ * Z' * A i)ᴴ * (∑ i, (A i)ᴴ * Z' * A i))).trace := by
  rw [← ks_defect A hK Z']
  obtain ⟨B, rfl⟩ := psd_factor ω hω
  rw [Finset.mul_sum, Matrix.trace_sum]
  refine Finset.sum_nonneg fun j _ => ?_
  set C := Z' * A j - A j * (∑ i, (A i)ᴴ * Z' * A i)
  have h1 : (Bᴴ * B * (Cᴴ * C)).trace = ((C * Bᴴ)ᴴ * (C * Bᴴ)).trace := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm Bᴴ]
    simp only [Matrix.mul_assoc]
  rw [h1]
  exact (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg

open scoped InnerProductSpace

lemma adj_contr {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (a : V →ₗ[ℂ] V) (ha : ∀ x, ‖a x‖ ≤ ‖x‖) (x : V) : ‖LinearMap.adjoint a x‖ ≤ ‖x‖ := by
  have h1 : ‖LinearMap.adjoint a x‖ ^ 2 = RCLike.re ⟪x, a (LinearMap.adjoint a x)⟫_ℂ := by
    rw [← LinearMap.adjoint_inner_left]; exact norm_sq_eq_re_inner (𝕜 := ℂ) _
  have h2 : RCLike.re ⟪x, a (LinearMap.adjoint a x)⟫_ℂ ≤ ‖x‖ * ‖a (LinearMap.adjoint a x)‖ :=
    re_inner_le_norm _ _
  have h3 := ha (LinearMap.adjoint a x)
  have h4 : 0 ≤ ‖x‖ := norm_nonneg _
  nlinarith [norm_nonneg (LinearMap.adjoint a x)]

lemma hs_swap {V W ι κ : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    [Fintype ι] [Fintype κ]
    (T : W →ₗ[ℂ] V) (bV : OrthonormalBasis κ ℂ V) (bW : OrthonormalBasis ι ℂ W) :
    ∑ i, ‖T (bW i)‖ ^ 2 = ∑ j, ‖LinearMap.adjoint T (bV j)‖ ^ 2 := by
  calc ∑ i, ‖T (bW i)‖ ^ 2 = ∑ i, ∑ j, ‖⟪bV j, T (bW i)⟫_ℂ‖ ^ 2 :=
        Finset.sum_congr rfl fun i _ => (bV.sum_sq_norm_inner_right _).symm
    _ = ∑ j, ∑ i, ‖⟪bV j, T (bW i)⟫_ℂ‖ ^ 2 := Finset.sum_comm
    _ = ∑ j, ∑ i, ‖⟪LinearMap.adjoint T (bV j), bW i⟫_ℂ‖ ^ 2 := by
        simp_rw [LinearMap.adjoint_inner_left]
    _ = ∑ j, ‖LinearMap.adjoint T (bV j)‖ ^ 2 :=
        Finset.sum_congr rfl fun j _ => bW.sum_sq_norm_inner_left _

/-- Trace argument (abstract form): `a`, `c` contractions, `a† R c = R` force `a R = R c`
and `‖R c y‖ = ‖R y‖`. -/
theorem trace_arg {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (a : V →ₗ[ℂ] V) (c : W →ₗ[ℂ] W) (R : W →ₗ[ℂ] V)
    (ha : ∀ x, ‖a x‖ ≤ ‖x‖) (hc : ∀ y, ‖c y‖ ≤ ‖y‖)
    (hR : ∀ y, LinearMap.adjoint a (R (c y)) = R y) (y : W) :
    a (R y) = R (c y) ∧ ‖R (c y)‖ = ‖R y‖ := by
  set bV := stdOrthonormalBasis ℂ V
  set bW := stdOrthonormalBasis ℂ W
  have hcadj : ∀ y, ‖LinearMap.adjoint c y‖ ≤ ‖y‖ := adj_contr c hc
  have hle : ∀ i ∈ (Finset.univ : Finset _),
      ‖LinearMap.adjoint a (R (c (bW i)))‖ ^ 2 ≤ ‖R (c (bW i))‖ ^ 2 :=
    fun i _ => pow_le_pow_left₀ (norm_nonneg _) (adj_contr a ha _) 2
  have e1 : ∑ i, ‖R (bW i)‖ ^ 2 = ∑ i, ‖LinearMap.adjoint a (R (c (bW i)))‖ ^ 2 := by
    simp_rw [hR]
  have e2 : ∑ i, ‖LinearMap.adjoint a (R (c (bW i)))‖ ^ 2 ≤ ∑ i, ‖R (c (bW i))‖ ^ 2 :=
    Finset.sum_le_sum hle
  have e3 : ∑ i, ‖R (c (bW i))‖ ^ 2 =
      ∑ j, ‖LinearMap.adjoint c (LinearMap.adjoint R (bV j))‖ ^ 2 := by
    have := hs_swap (R ∘ₗ c) bV bW
    simpa [LinearMap.adjoint_comp] using this
  have e4 : ∑ j, ‖LinearMap.adjoint c (LinearMap.adjoint R (bV j))‖ ^ 2 ≤
      ∑ j, ‖LinearMap.adjoint R (bV j)‖ ^ 2 :=
    Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hcadj _) 2
  have e5 := hs_swap R bV bW
  have hsum : ∑ i, ‖LinearMap.adjoint a (R (c (bW i)))‖ ^ 2 = ∑ i, ‖R (c (bW i))‖ ^ 2 :=
    le_antisymm e2 (by linarith)
  have heq : ∀ i, ‖LinearMap.adjoint a (R (c (bW i)))‖ ^ 2 = ‖R (c (bW i))‖ ^ 2 := fun i =>
    (Finset.sum_eq_sum_iff_of_le hle).1 hsum i (Finset.mem_univ i)
  have key : ∀ s : V, ‖LinearMap.adjoint a s‖ ^ 2 = ‖s‖ ^ 2 → a (LinearMap.adjoint a s) = s := by
    intro s hs
    have h1 : ‖LinearMap.adjoint a s‖ ^ 2 = RCLike.re ⟪s, a (LinearMap.adjoint a s)⟫_ℂ := by
      rw [← LinearMap.adjoint_inner_left]; exact norm_sq_eq_re_inner (𝕜 := ℂ) _
    have h2 := ha (LinearMap.adjoint a s)
    have h3 : ‖s - a (LinearMap.adjoint a s)‖ ^ 2 = ‖s‖ ^ 2
        - 2 * RCLike.re ⟪s, a (LinearMap.adjoint a s)⟫_ℂ + ‖a (LinearMap.adjoint a s)‖ ^ 2 :=
      norm_sub_sq (𝕜 := ℂ) _ _
    have h4 : ‖a (LinearMap.adjoint a s)‖ ^ 2 ≤ ‖LinearMap.adjoint a s‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h2 2
    have h5 : ‖s - a (LinearMap.adjoint a s)‖ ^ 2 ≤ 0 := by linarith
    have h6 : ‖s - a (LinearMap.adjoint a s)‖ = 0 := by
      nlinarith [norm_nonneg (s - a (LinearMap.adjoint a s))]
    exact (sub_eq_zero.1 (norm_eq_zero.1 h6)).symm
  have hlin : (a ∘ₗ LinearMap.adjoint a ∘ₗ R ∘ₗ c) = R ∘ₗ c := by
    apply bW.toBasis.ext
    intro i
    simp only [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply]
    exact key _ (heq i)
  have hy := LinearMap.congr_fun hlin y
  simp only [LinearMap.comp_apply] at hy
  refine ⟨?_, ?_⟩
  · rw [← hR y]; exact hy
  · rw [← hR y]
    have h1 : ‖LinearMap.adjoint a (R (c y))‖ ^ 2 =
        RCLike.re ⟪R (c y), a (LinearMap.adjoint a (R (c y)))⟫_ℂ := by
      rw [← LinearMap.adjoint_inner_left]; exact norm_sq_eq_re_inner (𝕜 := ℂ) _
    rw [hy, ← norm_sq_eq_re_inner (𝕜 := ℂ)] at h1
    exact ((pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1).symm


/-! ### Instantiation of the trace argument (faithful marginals) -/

/-- Heisenberg dual `Z ↦ ∑ Kᴴ E(Z) K` of a Kraus family with an embedding `E`. -/
noncomputable def heis {a c : Type} [Fintype c] {m : ℕ} (K : Fin m → Matrix c a ℂ)
    (E : Matrix a a ℂ →ₗ[ℂ] Matrix c c ℂ) (Z : Matrix a a ℂ) : Matrix a a ℂ :=
  ∑ k, (K k)ᴴ * E Z * K k

/-- A-side slice `Tr_B((1 ⊗ Y) ρ)`. -/
noncomputable def slc {a b : Type} [Fintype a] [DecidableEq a] [Fintype b]
    (ρ : Matrix (a × b) (a × b) ℂ) (Y : Matrix b b ℂ) : Matrix a a ℂ :=
  QAlgorithms.traceRight (((1 : Matrix a a ℂ) ⊗ₖ Y) * ρ)

lemma t_trR {a b : Type} [Fintype a] [Fintype b] [DecidableEq b]
    (Z : Matrix a a ℂ) (M : Matrix (a × b) (a × b) ℂ) :
    ((Z ⊗ₖ (1 : Matrix b b ℂ)) * M).trace = (Z * QAlgorithms.traceRight M).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, QAlgorithms.traceRight, Matrix.of_apply, Fintype.sum_prod_type,
    mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

lemma t_trL {a b : Type} [Fintype a] [DecidableEq a] [Fintype b]
    (Y : Matrix b b ℂ) (M : Matrix (a × b) (a × b) ℂ) :
    (((1 : Matrix a a ℂ) ⊗ₖ Y) * M).trace = (Y * QAlgorithms.traceLeft M).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, QAlgorithms.traceLeft, Matrix.of_apply, Fintype.sum_prod_type,
    mul_ite, ite_mul, one_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  trans ∑ y : a, ∑ x_1 : b, Y j x_1 * M (y, x_1) (y, j)
  · refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x_1 _ => by simp
  · exact Finset.sum_comm

lemma t_beta {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ) (Z : Matrix a a ℂ) (Y : Matrix b b ℂ) :
    (Z * slc ρ Y).trace = ((Z ⊗ₖ Y) * ρ).trace := by
  rw [slc, ← t_trR, ← Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
    Matrix.one_mul]

lemma slc_add {a b : Type} [Fintype a] [DecidableEq a] [Fintype b]
    (ρ : Matrix (a × b) (a × b) ℂ) (Y Y' : Matrix b b ℂ) :
    slc ρ (Y + Y') = slc ρ Y + slc ρ Y' := by
  ext i j
  simp [slc, QAlgorithms.traceRight, Matrix.kronecker_add, Matrix.add_mul,
    Finset.sum_add_distrib]

lemma slc_smul {a b : Type} [Fintype a] [DecidableEq a] [Fintype b]
    (ρ : Matrix (a × b) (a × b) ℂ) (r : ℂ) (Y : Matrix b b ℂ) :
    slc ρ (r • Y) = r • slc ρ Y := by
  ext i j
  simp [slc, QAlgorithms.traceRight, Matrix.kronecker_smul, Matrix.smul_mul, Finset.mul_sum]

lemma heis_add {a c : Type} [Fintype c] {m : ℕ} (K : Fin m → Matrix c a ℂ)
    (E : Matrix a a ℂ →ₗ[ℂ] Matrix c c ℂ) (Z W : Matrix a a ℂ) :
    heis K E (Z + W) = heis K E Z + heis K E W := by
  simp only [heis, map_add, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

lemma heis_smul {a c : Type} [Fintype c] {m : ℕ} (K : Fin m → Matrix c a ℂ)
    (E : Matrix a a ℂ →ₗ[ℂ] Matrix c c ℂ) (r : ℂ) (Z : Matrix a a ℂ) :
    heis K E (r • Z) = r • heis K E Z := by
  simp only [heis, map_smul, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

lemma heis_one {a c : Type} [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] {m : ℕ}
    (K : Fin m → Matrix c a ℂ) (hK : QAlgorithms.IsKrausFamily K)
    (E : Matrix a a ℂ →ₗ[ℂ] Matrix c c ℂ) (hE1 : E 1 = 1) : heis K E 1 = 1 := by
  simp only [heis, hE1, Matrix.mul_one]; exact hK

lemma heis_conj {a c : Type} [Fintype c] {m : ℕ} (K : Fin m → Matrix c a ℂ)
    (E : Matrix a a ℂ →ₗ[ℂ] Matrix c c ℂ) (hEH : ∀ Z, (E Z)ᴴ = E Zᴴ) (Z : Matrix a a ℂ) :
    (heis K E Z)ᴴ = heis K E Zᴴ := by
  simp only [heis, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hEH, Matrix.mul_assoc]

/-- `ω`-weighted Kadison–Schwarz in real-part form. -/
lemma heis_contr {a c : Type} [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] {m : ℕ}
    (K : Fin m → Matrix c a ℂ) (hK : QAlgorithms.IsKrausFamily K)
    (E : Matrix a a ℂ →ₗ[ℂ] Matrix c c ℂ) (hE : ∀ Z, (E Z)ᴴ * E Z = E (Zᴴ * Z))
    (ω : Matrix a a ℂ) (hω : ω.PosSemidef) (hinv : ∀ W, (ω * heis K E W).trace = (ω * W).trace)
    (Z : Matrix a a ℂ) :
    (ω * ((heis K E Z)ᴴ * heis K E Z)).trace.re ≤ (ω * (Zᴴ * Z)).trace.re := by
  have h := defect_nonneg K hK (E Z) ω hω
  rw [hE] at h
  have h2 : (ω * (∑ j, (K j)ᴴ * E (Zᴴ * Z) * K j)).trace = (ω * (Zᴴ * Z)).trace := hinv _
  rw [Matrix.mul_sub, Matrix.trace_sub, h2] at h
  have h3 := (Complex.le_def.1 h).1
  simp only [Complex.zero_re, Complex.sub_re] at h3
  simp only [heis]
  linarith

lemma t_im0 {a : Type} [Fintype a] [DecidableEq a] (ω W : Matrix a a ℂ) (hω : ω.PosSemidef) :
    (ω * (Wᴴ * W)).trace.im = 0 := by
  have h1 : (ω * (Wᴴ * W)).trace = (W * ω * Wᴴ).trace := by
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have h2 := (hω.mul_mul_conjTranspose_same W).trace_nonneg
  rw [h1]
  exact ((Complex.le_def.1 h2).2).symm

lemma t_conj {a : Type} [Fintype a] [DecidableEq a] (B W : Matrix a a ℂ) (hB : IsUnit B.det) :
    (B * W * B⁻¹).trace = W.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB, Matrix.one_mul]

/-- Vectorisation of square matrices into a Euclidean space (Frobenius inner product). -/
noncomputable def vecE (a : Type) [Fintype a] : Matrix a a ℂ ≃ₗ[ℂ] EuclideanSpace ℂ (a × a) :=
  (LinearEquiv.curry ℂ ℂ a a).symm.trans (WithLp.linearEquiv 2 ℂ (a × a → ℂ)).symm

lemma inner_vecE {a : Type} [Fintype a] (M N : Matrix a a ℂ) :
    ⟪vecE a M, vecE a N⟫_ℂ = (Mᴴ * N).trace := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  show ∑ p : a × a, N p.1 p.2 * star (M p.1 p.2) = _
  rw [Fintype.sum_prod_type]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _

lemma norm_vecE {a : Type} [Fintype a] (M : Matrix a a ℂ) :
    ‖vecE a M‖ ^ 2 = (Mᴴ * M).trace.re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_vecE]; rfl

/-- Linear map `M ↦ heis K E (M * P) * Q`. -/
noncomputable def sandL {a c : Type} [Fintype a] [Fintype c] {m : ℕ} (K : Fin m → Matrix c a ℂ)
    (E : Matrix a a ℂ →ₗ[ℂ] Matrix c c ℂ) (P Q : Matrix a a ℂ) :
    Matrix a a ℂ →ₗ[ℂ] Matrix a a ℂ where
  toFun M := heis K E (M * P) * Q
  map_add' x y := by simp only [Matrix.add_mul, heis_add]
  map_smul' r x := by simp only [Matrix.smul_mul, heis_smul, RingHom.id_apply]

/-- Linear map `N ↦ slc ρ (N * P) * Q`. -/
noncomputable def slcL {a b : Type} [Fintype a] [DecidableEq a] [Fintype b]
    (ρ : Matrix (a × b) (a × b) ℂ) (P : Matrix b b ℂ) (Q : Matrix a a ℂ) :
    Matrix b b ℂ →ₗ[ℂ] Matrix a a ℂ where
  toFun N := slc ρ (N * P) * Q
  map_add' x y := by simp only [Matrix.add_mul, slc_add]
  map_smul' r x := by simp only [Matrix.smul_mul, slc_smul, RingHom.id_apply]

set_option maxHeartbeats 1000000 in
/-- Trace argument, instantiated (faithful marginals): for `Z = X_Y ω⁻¹` the Heisenberg map
moves slices to slices, `Λ*(X_Y ω⁻¹) = X_{M* Y} ω⁻¹`, and `Z` intertwines every Kraus operator. -/
theorem trace_inst {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] {m n : ℕ}
    (ρ : Matrix (a × b) (a × b) ℂ) (K : Fin m → Matrix c a ℂ) (L : Fin n → Matrix d b ℂ)
    (hK : QAlgorithms.IsKrausFamily K) (hL : QAlgorithms.IsKrausFamily L)
    (Ea : Matrix a a ℂ →ₗ[ℂ] Matrix c c ℂ) (Eb : Matrix b b ℂ →ₗ[ℂ] Matrix d d ℂ)
    (hEa : ∀ Z, (Ea Z)ᴴ * Ea Z = Ea (Zᴴ * Z)) (hEb : ∀ Y, (Eb Y)ᴴ * Eb Y = Eb (Yᴴ * Y))
    (hEaH : ∀ Z, (Ea Z)ᴴ = Ea Zᴴ) (hEa1 : Ea 1 = 1) (hEb1 : Eb 1 = 1)
    (hbc : ∀ Z Y, ((heis K Ea Z ⊗ₖ heis L Eb Y) * ρ).trace = ((Z ⊗ₖ Y) * ρ).trace)
    (hωA : (QAlgorithms.traceRight ρ).PosSemidef) (hωB : (QAlgorithms.traceLeft ρ).PosSemidef)
    (huA : IsUnit (QAlgorithms.traceRight ρ).det) (huB : IsUnit (QAlgorithms.traceLeft ρ).det)
    (Y : Matrix b b ℂ) :
    heis K Ea (slc ρ Y * (QAlgorithms.traceRight ρ)⁻¹) =
        slc ρ (heis L Eb Y) * (QAlgorithms.traceRight ρ)⁻¹ ∧
      ∀ k, Ea (slc ρ Y * (QAlgorithms.traceRight ρ)⁻¹) * K k =
        K k * heis K Ea (slc ρ Y * (QAlgorithms.traceRight ρ)⁻¹) := by
  set ω := QAlgorithms.traceRight ρ with hωdef
  set ωB := QAlgorithms.traceLeft ρ with hωBdef
  have hinvA : ∀ W, (ω * heis K Ea W).trace = (ω * W).trace := by
    intro W
    have h := hbc W 1
    rw [heis_one L hL Eb hEb1, t_trR, t_trR] at h
    rw [Matrix.trace_mul_comm ω, Matrix.trace_mul_comm ω]
    exact h
  have hinvB : ∀ W, (ωB * heis L Eb W).trace = (ωB * W).trace := by
    intro W
    have h := hbc 1 W
    rw [heis_one K hK Ea hEa1, t_trL, t_trL] at h
    rw [Matrix.trace_mul_comm ωB, Matrix.trace_mul_comm ωB]
    exact h
  obtain ⟨B, hB⟩ := psd_factor ω hωA
  obtain ⟨C, hC⟩ := psd_factor ωB hωB
  have hBB : IsUnit (Bᴴ.det * B.det) := by
    have h := huA; rw [hB, Matrix.det_mul] at h; exact h
  have hCC : IsUnit (Cᴴ.det * C.det) := by
    have h := huB; rw [hC, Matrix.det_mul] at h; exact h
  have hBu : IsUnit B.det := isUnit_of_mul_isUnit_right hBB
  have hBHu : IsUnit Bᴴ.det := isUnit_of_mul_isUnit_left hBB
  have hCHu : IsUnit Cᴴ.det := isUnit_of_mul_isUnit_left hCC
  have hωinv : ω⁻¹ = B⁻¹ * (Bᴴ)⁻¹ := by rw [hB, Matrix.mul_inv_rev]
  set aL : EuclideanSpace ℂ (a × a) →ₗ[ℂ] EuclideanSpace ℂ (a × a) :=
    (vecE a).toLinearMap ∘ₗ sandL K Ea (Bᴴ)⁻¹ Bᴴ ∘ₗ (vecE a).symm.toLinearMap with haL
  set cL : EuclideanSpace ℂ (b × b) →ₗ[ℂ] EuclideanSpace ℂ (b × b) :=
    (vecE b).toLinearMap ∘ₗ sandL L Eb (Cᴴ)⁻¹ Cᴴ ∘ₗ (vecE b).symm.toLinearMap with hcL
  set RL : EuclideanSpace ℂ (b × b) →ₗ[ℂ] EuclideanSpace ℂ (a × a) :=
    (vecE a).toLinearMap ∘ₗ slcL ρ (Cᴴ)⁻¹ B⁻¹ ∘ₗ (vecE b).symm.toLinearMap with hRL
  have haL_apply : ∀ M, aL (vecE a M) = vecE a (heis K Ea (M * (Bᴴ)⁻¹) * Bᴴ) := fun M => by
    simp [haL, sandL]
  have hcL_apply : ∀ N, cL (vecE b N) = vecE b (heis L Eb (N * (Cᴴ)⁻¹) * Cᴴ) := fun N => by
    simp [hcL, sandL]
  have hRL_apply : ∀ N, RL (vecE b N) = vecE a (slc ρ (N * (Cᴴ)⁻¹) * B⁻¹) := fun N => by
    simp [hRL, slcL]
  have nB : ∀ W, ‖vecE a (W * Bᴴ)‖ ^ 2 = (ω * (Wᴴ * W)).trace.re := by
    intro W
    rw [norm_vecE, hB, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    congr 1
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have nC : ∀ W, ‖vecE b (W * Cᴴ)‖ ^ 2 = (ωB * (Wᴴ * W)).trace.re := by
    intro W
    rw [norm_vecE, hC, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    congr 1
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have ha : ∀ x, ‖aL x‖ ≤ ‖x‖ := by
    intro x
    obtain ⟨M, rfl⟩ := (vecE a).surjective x
    have hM : M * (Bᴴ)⁻¹ * Bᴴ = M := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBHu, Matrix.mul_one]
    have e1 := nB (heis K Ea (M * (Bᴴ)⁻¹))
    have e2 := nB (M * (Bᴴ)⁻¹)
    rw [hM] at e2
    rw [haL_apply]
    have hc := heis_contr K hK Ea hEa ω hωA hinvA (M * (Bᴴ)⁻¹)
    nlinarith [norm_nonneg (vecE a (heis K Ea (M * (Bᴴ)⁻¹) * Bᴴ)), norm_nonneg (vecE a M)]
  have hc : ∀ y, ‖cL y‖ ≤ ‖y‖ := by
    intro y
    obtain ⟨N, rfl⟩ := (vecE b).surjective y
    have hN : N * (Cᴴ)⁻¹ * Cᴴ = N := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hCHu, Matrix.mul_one]
    have e1 := nC (heis L Eb (N * (Cᴴ)⁻¹))
    have e2 := nC (N * (Cᴴ)⁻¹)
    rw [hN] at e2
    rw [hcL_apply]
    have hc := heis_contr L hL Eb hEb ωB hωB hinvB (N * (Cᴴ)⁻¹)
    nlinarith [norm_nonneg (vecE b (heis L Eb (N * (Cᴴ)⁻¹) * Cᴴ)), norm_nonneg (vecE b N)]
  have hR : ∀ y, LinearMap.adjoint aL (RL (cL y)) = RL y := by
    intro y
    apply ext_inner_left ℂ
    intro x
    rw [LinearMap.adjoint_inner_right]
    obtain ⟨M, rfl⟩ := (vecE a).surjective x
    obtain ⟨N, rfl⟩ := (vecE b).surjective y
    rw [hcL_apply, hRL_apply, hRL_apply, haL_apply, inner_vecE, inner_vecE,
      Matrix.mul_assoc (heis L Eb _) Cᴴ, Matrix.mul_nonsing_inv _ hCHu, Matrix.mul_one,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, heis_conj K Ea hEaH,
      ← Matrix.mul_assoc, Matrix.mul_assoc B, t_conj B _ hBu, t_beta, hbc, ← t_beta,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm (B⁻¹ * Mᴴ)]
    rw [Matrix.trace_mul_comm Mᴴ, Matrix.mul_assoc]
  obtain ⟨h1, h2⟩ := trace_arg aL cL RL ha hc hR (vecE b (Y * Cᴴ))
  have eY : Y * Cᴴ * (Cᴴ)⁻¹ = Y := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hCHu, Matrix.mul_one]
  rw [hRL_apply, hcL_apply, hRL_apply, eY, haL_apply, Matrix.mul_assoc (heis L Eb Y) Cᴴ,
    Matrix.mul_nonsing_inv _ hCHu, Matrix.mul_one] at h1
  rw [hcL_apply, hRL_apply, hRL_apply, eY, Matrix.mul_assoc (heis L Eb Y) Cᴴ,
    Matrix.mul_nonsing_inv _ hCHu, Matrix.mul_one] at h2
  simp only [Matrix.mul_assoc] at h1
  have hA := (vecE a).injective h1
  have hZB : slc ρ Y * (B⁻¹ * (Bᴴ)⁻¹) * Bᴴ = slc ρ Y * B⁻¹ := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBHu, Matrix.mul_one]
  have part1 : heis K Ea (slc ρ Y * (B⁻¹ * (Bᴴ)⁻¹)) =
      slc ρ (heis L Eb Y) * (B⁻¹ * (Bᴴ)⁻¹) := by
    have h := congrArg (· * (Bᴴ)⁻¹) hA
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBHu, Matrix.mul_one] at h
    exact h
  have hn : ‖vecE a (heis K Ea (slc ρ Y * (B⁻¹ * (Bᴴ)⁻¹)) * Bᴴ)‖ =
      ‖vecE a (slc ρ Y * (B⁻¹ * (Bᴴ)⁻¹) * Bᴴ)‖ := by
    rw [h1, hZB]; exact h2
  have hre : (ω * ((heis K Ea (slc ρ Y * (B⁻¹ * (Bᴴ)⁻¹)))ᴴ *
      heis K Ea (slc ρ Y * (B⁻¹ * (Bᴴ)⁻¹)))).trace.re =
      (ω * ((slc ρ Y * (B⁻¹ * (Bᴴ)⁻¹))ᴴ * (slc ρ Y * (B⁻¹ * (Bᴴ)⁻¹)))).trace.re := by
    rw [← nB, ← nB, hn]
  have hdef : (ω * ((∑ j, (K j)ᴴ * ((Ea (slc ρ Y * (B⁻¹ * (Bᴴ)⁻¹)))ᴴ *
      Ea (slc ρ Y * (B⁻¹ * (Bᴴ)⁻¹))) * K j) -
      (∑ i, (K i)ᴴ * Ea (slc ρ Y * (B⁻¹ * (Bᴴ)⁻¹)) * K i)ᴴ *
      (∑ i, (K i)ᴴ * Ea (slc ρ Y * (B⁻¹ * (Bᴴ)⁻¹)) * K i))).trace = 0 := by
    have e := hinvA ((slc ρ Y * (B⁻¹ * (Bᴴ)⁻¹))ᴴ * (slc ρ Y * (B⁻¹ * (Bᴴ)⁻¹)))
    simp only [heis] at e hre
    rw [hEa, Matrix.mul_sub, Matrix.trace_sub, e]
    apply Complex.ext
    · rw [Complex.sub_re, hre, sub_self, Complex.zero_re]
    · rw [Complex.sub_im, t_im0 ω _ hωA, t_im0 ω _ hωA, sub_self, Complex.zero_im]
  have hint := intertwine_of_defect K hK (Ea (slc ρ Y * (B⁻¹ * (Bᴴ)⁻¹))) ω hωA hdef
  rw [hωinv]
  refine ⟨part1, fun k => ?_⟩
  have h := congrArg (· * ω⁻¹) (hint k)
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ huA, Matrix.mul_one,
    Matrix.zero_mul] at h
  simp only [heis, Matrix.mul_assoc]
  exact sub_eq_zero.1 h


/-- Kernel argument: if `T` is isometric on a finite-dimensional subspace `G` (and maps it into
itself) and `‖Φ (T x)‖ ≤ ‖Φ x‖` on `G`, then equality holds on `G` (the sum of `‖Φ eᵢ‖²` over an
orthonormal basis of `G` does not depend on the basis). -/
theorem kernel_arg {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (G : Submodule ℂ V) (T : V →ₗ[ℂ] V) (Φ : V →ₗ[ℂ] W)
    (hTG : ∀ x ∈ G, T x ∈ G) (hTn : ∀ x ∈ G, ‖T x‖ = ‖x‖)
    (hΦ : ∀ x ∈ G, ‖Φ (T x)‖ ≤ ‖Φ x‖) (x : V) (hx : x ∈ G) : ‖Φ (T x)‖ = ‖Φ x‖ := by
  let U : G →ₗᵢ[ℂ] G :=
    { toLinearMap := T.restrict hTG
      norm_map' := fun y => by
        show ‖T y‖ = ‖(y : V)‖
        exact hTn y y.2 }
  let Ue : G ≃ₗᵢ[ℂ] G := U.toLinearIsometryEquiv rfl
  let ψ : G →ₗ[ℂ] W := Φ ∘ₗ G.subtype
  have hsum : ∀ {ι : Type} [Fintype ι] (e : OrthonormalBasis ι ℂ G),
      ∑ i, ‖Φ (T (e i))‖ ^ 2 = ∑ i, ‖Φ (e i)‖ ^ 2 := by
    intro ι _ e
    have h1 := hs_swap ψ (stdOrthonormalBasis ℂ W) e
    have h2 := hs_swap ψ (stdOrthonormalBasis ℂ W) (e.map Ue)
    simp only [OrthonormalBasis.map_apply] at h2
    rw [← h1] at h2
    exact h2
  by_cases hx0 : x = 0
  · subst hx0; simp
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx0
  set u : V := ((‖x‖ : ℂ)⁻¹) • x with hu
  have huG : u ∈ G := G.smul_mem _ hx
  have hun : ‖(⟨u, huG⟩ : G)‖ = 1 := by
    show ‖u‖ = 1
    rw [hu, norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hxn]
  have hon : Orthonormal ℂ ((↑) : ({(⟨u, huG⟩ : G)} : Set G) → G) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    rw [Set.mem_singleton_iff] at hi hj
    subst hi; subst hj
    simp [inner_self_eq_norm_sq_to_K, hun]
  obtain ⟨s, b, hsub, hb⟩ := hon.exists_orthonormalBasis_extension
  have hmem : (⟨u, huG⟩ : G) ∈ s := hsub (Set.mem_singleton _)
  have hle : ∀ i ∈ (Finset.univ : Finset s), ‖Φ (T (b i))‖ ^ 2 ≤ ‖Φ (b i)‖ ^ 2 :=
    fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hΦ _ (b i).2) 2
  have heq := (Finset.sum_eq_sum_iff_of_le hle).1 (hsum b) ⟨_, hmem⟩ (Finset.mem_univ _)
  have hbi : b ⟨_, hmem⟩ = ⟨u, huG⟩ := by rw [hb]
  rw [hbi] at heq
  change ‖Φ (T u)‖ ^ 2 = ‖Φ u‖ ^ 2 at heq
  have heq' : ‖Φ (T u)‖ = ‖Φ u‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 heq
  have hxu : x = (‖x‖ : ℂ) • u := by
    rw [hu, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hxn), one_smul]
  rw [hxu]
  simp only [map_smul, norm_smul, heq']

/-! ### R1: broadcast duality from the marginal conditions -/

/-- `Z ↦ Z ⊗ 1` (original-copy embedding on `a × a`). -/
noncomputable def kronR (a : Type) [Fintype a] [DecidableEq a] :
    Matrix a a ℂ →ₗ[ℂ] Matrix (a × a) (a × a) ℂ where
  toFun Z := Z ⊗ₖ (1 : Matrix a a ℂ)
  map_add' Z W := Matrix.add_kronecker Z W 1
  map_smul' c Z := Matrix.smul_kronecker c Z 1

/-- `Z ↦ 1 ⊗ Z` (second-copy embedding on `a × a`). -/
noncomputable def kronL (a : Type) [Fintype a] [DecidableEq a] :
    Matrix a a ℂ →ₗ[ℂ] Matrix (a × a) (a × a) ℂ where
  toFun Z := (1 : Matrix a a ℂ) ⊗ₖ Z
  map_add' Z W := Matrix.kronecker_add 1 Z W
  map_smul' c Z := Matrix.kronecker_smul c 1 Z

lemma kronR_apply {a : Type} [Fintype a] [DecidableEq a] (Z : Matrix a a ℂ) :
    kronR a Z = Z ⊗ₖ (1 : Matrix a a ℂ) := rfl

lemma kronL_apply {a : Type} [Fintype a] [DecidableEq a] (Z : Matrix a a ℂ) :
    kronL a Z = (1 : Matrix a a ℂ) ⊗ₖ Z := rfl

lemma kronR_mul {a : Type} [Fintype a] [DecidableEq a] (Z : Matrix a a ℂ) :
    (kronR a Z)ᴴ * kronR a Z = kronR a (Zᴴ * Z) := by
  rw [kronR_apply, kronR_apply, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.mul_one]

lemma kronL_mul {a : Type} [Fintype a] [DecidableEq a] (Z : Matrix a a ℂ) :
    (kronL a Z)ᴴ * kronL a Z = kronL a (Zᴴ * Z) := by
  rw [kronL_apply, kronL_apply, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.mul_one]

lemma kronR_H {a : Type} [Fintype a] [DecidableEq a] (Z : Matrix a a ℂ) :
    (kronR a Z)ᴴ = kronR a Zᴴ := by
  rw [kronR_apply, kronR_apply, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

lemma kronL_H {a : Type} [Fintype a] [DecidableEq a] (Z : Matrix a a ℂ) :
    (kronL a Z)ᴴ = kronL a Zᴴ := by
  rw [kronL_apply, kronL_apply, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

lemma kronR_one {a : Type} [Fintype a] [DecidableEq a] : kronR a 1 = 1 := by
  rw [kronR_apply, Matrix.one_kronecker_one]

lemma kronL_one {a : Type} [Fintype a] [DecidableEq a] : kronL a 1 = 1 := by
  rw [kronL_apply, Matrix.one_kronecker_one]

/-- Heisenberg pairing with a local channel: `Tr((Λ*(A) ⊗ Γ*(B)) ρ) = Tr((A ⊗ B)(Λ⊗Γ)[ρ])`. -/
lemma tr_local {a a₁ b b₁ : Type} [Fintype a] [Fintype a₁] [Fintype b] [Fintype b₁] {m n : ℕ}
    (K : Fin m → Matrix a₁ a ℂ) (L : Fin n → Matrix b₁ b ℂ)
    (A : Matrix a₁ a₁ ℂ) (B : Matrix b₁ b₁ ℂ) (ρ : Matrix (a × b) (a × b) ℂ) :
    (((∑ k, (K k)ᴴ * A * K k) ⊗ₖ (∑ l, (L l)ᴴ * B * L l)) * ρ).trace =
      ((A ⊗ₖ B) * NoLocalBroadcast.Broadcast.localApply K L ρ).trace := by
  have hterm : ∀ k l, ((K k)ᴴ * A * K k) ⊗ₖ ((L l)ᴴ * B * L l) =
      (K k ⊗ₖ L l)ᴴ * (A ⊗ₖ B) * (K k ⊗ₖ L l) := by
    intro k l
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rw [sum_kron]
  simp_rw [kron_sum, hterm]
  rw [NoLocalBroadcast.Broadcast.localApply, QAlgorithms.krausApply]
  simp only [Finset.sum_mul, Matrix.mul_sum, Matrix.trace_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
    Matrix.mul_assoc]

lemma sum_rot3 {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℂ) :
    ∑ i, ∑ j, ∑ k, f i j k = ∑ j, ∑ k, ∑ i, f i j k := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_comm

lemma sum_rot4 {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ j, ∑ k, ∑ l, ∑ i, f i j k l := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => sum_rot3 _

lemma tr_copies {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (σ : Matrix ((a × a) × (b × b)) ((a × a) × (b × b)) ℂ) (Z : Matrix a a ℂ) (Y : Matrix b b ℂ) :
    (((Z ⊗ₖ (1 : Matrix a a ℂ)) ⊗ₖ (Y ⊗ₖ (1 : Matrix b b ℂ))) * σ).trace =
      ((Z ⊗ₖ Y) * NoLocalBroadcast.Broadcast.traceCopies σ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, NoLocalBroadcast.Broadcast.traceCopies, Matrix.of_apply,
    Fintype.sum_prod_type, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, Finset.sum_ite_irrel, Finset.sum_const_zero]
  refine Finset.sum_congr rfl fun x _ => ?_
  trans ∑ x' : a, ∑ y : b, ∑ u : a, ∑ v : b, ∑ y' : b,
    Z x u * Y y v * σ ((u, x'), v, y') ((x, x'), y, y')
  · exact Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun y _ => sum_rot3 _
  · exact sum_rot4 _

lemma tr_originals {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (σ : Matrix ((a × a) × (b × b)) ((a × a) × (b × b)) ℂ) (Z : Matrix a a ℂ) (Y : Matrix b b ℂ) :
    ((((1 : Matrix a a ℂ) ⊗ₖ Z) ⊗ₖ ((1 : Matrix b b ℂ) ⊗ₖ Y)) * σ).trace =
      ((Z ⊗ₖ Y) * NoLocalBroadcast.Broadcast.traceOriginals σ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, NoLocalBroadcast.Broadcast.traceOriginals, Matrix.of_apply,
    Fintype.sum_prod_type, mul_ite, ite_mul, one_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun xz _ => ?_
  trans ∑ s : a, ∑ y : b, ∑ u : a, ∑ v : b, ∑ t : b,
    Z xz u * Y y v * σ ((s, u), t, v) ((s, xz), t, y)
  · exact Finset.sum_congr rfl fun s _ => sum_rot4 _
  · exact sum_rot4 _


/-- R1 (copies): `σ_X = ρ` gives the broadcast duality for the embeddings `Z ↦ Z ⊗ 1`. -/
theorem bc_copies {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {m n : ℕ}
    (ρ : Matrix (a × b) (a × b) ℂ) (K : Fin m → Matrix (a × a) a ℂ) (L : Fin n → Matrix (b × b) b ℂ)
    (h : NoLocalBroadcast.Broadcast.traceCopies (NoLocalBroadcast.Broadcast.localApply K L ρ) = ρ)
    (Z : Matrix a a ℂ) (Y : Matrix b b ℂ) :
    ((heis K (kronR a) Z ⊗ₖ heis L (kronR b) Y) * ρ).trace = ((Z ⊗ₖ Y) * ρ).trace := by
  rw [heis, heis, tr_local, kronR_apply, kronR_apply, tr_copies, h]

/-- R1 (originals): `σ_Y = ρ` gives the broadcast duality for the embeddings `Z ↦ 1 ⊗ Z`. -/
theorem bc_originals {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {m n : ℕ} (ρ : Matrix (a × b) (a × b) ℂ) (K : Fin m → Matrix (a × a) a ℂ)
    (L : Fin n → Matrix (b × b) b ℂ)
    (h : NoLocalBroadcast.Broadcast.traceOriginals (NoLocalBroadcast.Broadcast.localApply K L ρ) = ρ)
    (Z : Matrix a a ℂ) (Y : Matrix b b ℂ) :
    ((heis K (kronL a) Z ⊗ₖ heis L (kronL b) Y) * ρ).trace = ((Z ⊗ₖ Y) * ρ).trace := by
  rw [heis, heis, tr_local, kronL_apply, kronL_apply, tr_originals, h]

set_option maxHeartbeats 1000000 in
/-- R2 (adjoint intertwining): for `Z = X_Y ω⁻¹` also `Zᴴ` intertwines the Kraus operators.
`Λ*` is `ω`-isometric on `G`, `‖B Λ*(Z)‖ ≤ ‖B Z‖` (Kadison–Schwarz for `Zᴴ`), so `kernel_arg`
forces equality, i.e. the defect of `E(Zᴴ)` vanishes. -/
theorem adj_inst {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] {m n : ℕ}
    (ρ : Matrix (a × b) (a × b) ℂ) (K : Fin m → Matrix c a ℂ) (L : Fin n → Matrix d b ℂ)
    (hK : QAlgorithms.IsKrausFamily K) (hL : QAlgorithms.IsKrausFamily L)
    (Ea : Matrix a a ℂ →ₗ[ℂ] Matrix c c ℂ) (Eb : Matrix b b ℂ →ₗ[ℂ] Matrix d d ℂ)
    (hEa : ∀ Z, (Ea Z)ᴴ * Ea Z = Ea (Zᴴ * Z)) (hEb : ∀ Y, (Eb Y)ᴴ * Eb Y = Eb (Yᴴ * Y))
    (hEaH : ∀ Z, (Ea Z)ᴴ = Ea Zᴴ) (hEa1 : Ea 1 = 1) (hEb1 : Eb 1 = 1)
    (hbc : ∀ Z Y, ((heis K Ea Z ⊗ₖ heis L Eb Y) * ρ).trace = ((Z ⊗ₖ Y) * ρ).trace)
    (hωA : (QAlgorithms.traceRight ρ).PosSemidef) (hωB : (QAlgorithms.traceLeft ρ).PosSemidef)
    (huA : IsUnit (QAlgorithms.traceRight ρ).det) (huB : IsUnit (QAlgorithms.traceLeft ρ).det)
    (Y : Matrix b b ℂ) :
    ∀ k, Ea ((slc ρ Y * (QAlgorithms.traceRight ρ)⁻¹)ᴴ) * K k =
        K k * heis K Ea ((slc ρ Y * (QAlgorithms.traceRight ρ)⁻¹)ᴴ) := by
  have hti := fun Y' => trace_inst ρ K L hK hL Ea Eb hEa hEb hEaH hEa1 hEb1 hbc hωA hωB huA huB Y'
  set ω := QAlgorithms.traceRight ρ with hωdef
  have hK' : (∑ j, (K j)ᴴ * K j) = 1 := hK
  have hinvA : ∀ W, (ω * heis K Ea W).trace = (ω * W).trace := by
    intro W
    have h := hbc W 1
    rw [heis_one L hL Eb hEb1, t_trR, t_trR] at h
    rw [Matrix.trace_mul_comm ω, Matrix.trace_mul_comm ω]
    exact h
  obtain ⟨B, hB⟩ := psd_factor ω hωA
  have hBB : IsUnit (Bᴴ.det * B.det) := by
    have h := huA; rw [hB, Matrix.det_mul] at h; exact h
  have hBHu : IsUnit Bᴴ.det := isUnit_of_mul_isUnit_left hBB
  set aL : EuclideanSpace ℂ (a × a) →ₗ[ℂ] EuclideanSpace ℂ (a × a) :=
    (vecE a).toLinearMap ∘ₗ sandL K Ea (Bᴴ)⁻¹ Bᴴ ∘ₗ (vecE a).symm.toLinearMap with haL
  have haL_apply : ∀ M, aL (vecE a M) = vecE a (heis K Ea (M * (Bᴴ)⁻¹) * Bᴴ) := fun M => by
    simp [haL, sandL]
  set Φ : EuclideanSpace ℂ (a × a) →ₗ[ℂ] EuclideanSpace ℂ (a × a) :=
    (vecE a).toLinearMap ∘ₗ (LinearMap.mulLeft ℂ B ∘ₗ LinearMap.mulRight ℂ (Bᴴ)⁻¹) ∘ₗ
      (vecE a).symm.toLinearMap with hΦdef
  have hΦ_apply : ∀ M, Φ (vecE a M) = vecE a (B * (M * (Bᴴ)⁻¹)) := fun M => by
    simp [hΦdef, Matrix.mul_assoc]
  set Gs : Submodule ℂ (EuclideanSpace ℂ (a × a)) :=
    LinearMap.range ((vecE a).toLinearMap ∘ₗ slcL ρ 1 (ω⁻¹ * Bᴴ)) with hGs
  have hG : ∀ Y', vecE a (slc ρ Y' * ω⁻¹ * Bᴴ) ∈ Gs := fun Y' =>
    ⟨Y', by simp [slcL, Matrix.mul_assoc]⟩
  have hmem : ∀ x ∈ Gs, ∃ Y', x = vecE a (slc ρ Y' * ω⁻¹ * Bᴴ) := by
    rintro x ⟨Y', rfl⟩
    exact ⟨Y', by simp [slcL, Matrix.mul_assoc]⟩
  have nB : ∀ W, ‖vecE a (W * Bᴴ)‖ ^ 2 = (ω * (Wᴴ * W)).trace.re := by
    intro W
    rw [norm_vecE, hB, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    congr 1
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have nB' : ∀ W, ‖vecE a (B * W)‖ ^ 2 = (ω * (W * Wᴴ)).trace.re := by
    intro W
    rw [norm_vecE, hB, Matrix.conjTranspose_mul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm Wᴴ]
    simp only [Matrix.mul_assoc]
  have hZB : ∀ Z : Matrix a a ℂ, Z * Bᴴ * (Bᴴ)⁻¹ = Z := fun Z => by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBHu, Matrix.mul_one]
  have haLZ : ∀ Z, aL (vecE a (Z * Bᴴ)) = vecE a (heis K Ea Z * Bᴴ) := by
    intro Z; rw [haL_apply, hZB]
  have hΦZ : ∀ Z, Φ (vecE a (Z * Bᴴ)) = vecE a (B * Z) := by
    intro Z; rw [hΦ_apply, hZB]
  have hTG : ∀ x ∈ Gs, aL x ∈ Gs := by
    intro x hx
    obtain ⟨Y', rfl⟩ := hmem x hx
    rw [haLZ, (hti Y').1]
    exact hG _
  have hTn : ∀ x ∈ Gs, ‖aL x‖ = ‖x‖ := by
    intro x hx
    obtain ⟨Y', rfl⟩ := hmem x hx
    rw [haLZ]
    have hint := (hti Y').2
    set Z := slc ρ Y' * ω⁻¹ with hZ
    have e : ∀ k, (K k)ᴴ * Ea (Zᴴ * Z) * K k =
        (heis K Ea Z)ᴴ * ((K k)ᴴ * K k) * heis K Ea Z := by
      intro k
      rw [← hEa, show (K k)ᴴ * ((Ea Z)ᴴ * Ea Z) * K k = (Ea Z * K k)ᴴ * (Ea Z * K k) by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc], hint k,
        Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    have hsq : (heis K Ea Z)ᴴ * heis K Ea Z = heis K Ea (Zᴴ * Z) := by
      conv_rhs => rw [heis]
      rw [Finset.sum_congr rfl fun k _ => e k, ← Finset.sum_mul, ← Finset.mul_sum, hK',
        Matrix.mul_one]
    have h2 : ‖vecE a (heis K Ea Z * Bᴴ)‖ ^ 2 = ‖vecE a (Z * Bᴴ)‖ ^ 2 := by
      rw [nB, nB, hsq, hinvA]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  have hΦle : ∀ x ∈ Gs, ‖Φ (aL x)‖ ≤ ‖Φ x‖ := by
    intro x hx
    obtain ⟨Y', rfl⟩ := hmem x hx
    rw [haLZ, hΦZ, hΦZ]
    set Z := slc ρ Y' * ω⁻¹ with hZ
    have hc := heis_contr K hK Ea hEa ω hωA hinvA Zᴴ
    rw [← heis_conj K Ea hEaH Z] at hc
    simp only [Matrix.conjTranspose_conjTranspose] at hc
    have e1 := nB' (heis K Ea Z)
    have e2 := nB' Z
    nlinarith [norm_nonneg (vecE a (B * heis K Ea Z)), norm_nonneg (vecE a (B * Z))]
  have keq := kernel_arg Gs aL Φ hTG hTn hΦle _ (hG Y)
  set Z0 := slc ρ Y * ω⁻¹ with hZ0
  rw [haLZ, hΦZ, hΦZ] at keq
  have hre : (ω * (heis K Ea Z0 * (heis K Ea Z0)ᴴ)).trace.re = (ω * (Z0 * Z0ᴴ)).trace.re := by
    rw [← nB', ← nB', keq]
  have im1 := t_im0 ω Z0ᴴ hωA
  have im2 := t_im0 ω (heis K Ea Z0)ᴴ hωA
  simp only [Matrix.conjTranspose_conjTranspose] at im1 im2
  have hdef : (ω * ((∑ j, (K j)ᴴ * ((Ea Z0ᴴ)ᴴ * Ea Z0ᴴ) * K j) -
      (∑ i, (K i)ᴴ * Ea Z0ᴴ * K i)ᴴ * (∑ i, (K i)ᴴ * Ea Z0ᴴ * K i))).trace = 0 := by
    have e := hinvA (Z0 * Z0ᴴ)
    rw [hEa, Matrix.conjTranspose_conjTranspose]
    change (ω * (heis K Ea (Z0 * Z0ᴴ) - (heis K Ea Z0ᴴ)ᴴ * heis K Ea Z0ᴴ)).trace = 0
    rw [← heis_conj K Ea hEaH Z0, Matrix.conjTranspose_conjTranspose, Matrix.mul_sub,
      Matrix.trace_sub, e]
    apply Complex.ext
    · rw [Complex.sub_re, hre, sub_self, Complex.zero_re]
    · rw [Complex.sub_im, im1, im2, sub_self, Complex.zero_im]
  have hint := intertwine_of_defect K hK (Ea Z0ᴴ) ω hωA hdef
  intro k
  have h := congrArg (· * ω⁻¹) (hint k)
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ huA, Matrix.mul_one,
    Matrix.zero_mul] at h
  simp only [heis, Matrix.mul_assoc]
  exact sub_eq_zero.1 h

set_option maxHeartbeats 1000000 in
/-- Surjectivity of `Λ*` on `G = {X_Y ω⁻¹}` (an isometry of a finite-dimensional space). -/
theorem surj_inst {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] {m n : ℕ}
    (ρ : Matrix (a × b) (a × b) ℂ) (K : Fin m → Matrix c a ℂ) (L : Fin n → Matrix d b ℂ)
    (hK : QAlgorithms.IsKrausFamily K) (hL : QAlgorithms.IsKrausFamily L)
    (Ea : Matrix a a ℂ →ₗ[ℂ] Matrix c c ℂ) (Eb : Matrix b b ℂ →ₗ[ℂ] Matrix d d ℂ)
    (hEa : ∀ Z, (Ea Z)ᴴ * Ea Z = Ea (Zᴴ * Z)) (hEb : ∀ Y, (Eb Y)ᴴ * Eb Y = Eb (Yᴴ * Y))
    (hEaH : ∀ Z, (Ea Z)ᴴ = Ea Zᴴ) (hEa1 : Ea 1 = 1) (hEb1 : Eb 1 = 1)
    (hbc : ∀ Z Y, ((heis K Ea Z ⊗ₖ heis L Eb Y) * ρ).trace = ((Z ⊗ₖ Y) * ρ).trace)
    (hωA : (QAlgorithms.traceRight ρ).PosSemidef) (hωB : (QAlgorithms.traceLeft ρ).PosSemidef)
    (huA : IsUnit (QAlgorithms.traceRight ρ).det) (huB : IsUnit (QAlgorithms.traceLeft ρ).det)
    (Y : Matrix b b ℂ) :
    ∃ Y', heis K Ea (slc ρ Y' * (QAlgorithms.traceRight ρ)⁻¹) =
        slc ρ Y * (QAlgorithms.traceRight ρ)⁻¹ := by
  have hti := fun Y' => trace_inst ρ K L hK hL Ea Eb hEa hEb hEaH hEa1 hEb1 hbc hωA hωB huA huB Y'
  set ω := QAlgorithms.traceRight ρ with hωdef
  have hK' : (∑ j, (K j)ᴴ * K j) = 1 := hK
  have hinvA : ∀ W, (ω * heis K Ea W).trace = (ω * W).trace := by
    intro W
    have h := hbc W 1
    rw [heis_one L hL Eb hEb1, t_trR, t_trR] at h
    rw [Matrix.trace_mul_comm ω, Matrix.trace_mul_comm ω]
    exact h
  obtain ⟨B, hB⟩ := psd_factor ω hωA
  have hBB : IsUnit (Bᴴ.det * B.det) := by
    have h := huA; rw [hB, Matrix.det_mul] at h; exact h
  have hBHu : IsUnit Bᴴ.det := isUnit_of_mul_isUnit_left hBB
  set aL : EuclideanSpace ℂ (a × a) →ₗ[ℂ] EuclideanSpace ℂ (a × a) :=
    (vecE a).toLinearMap ∘ₗ sandL K Ea (Bᴴ)⁻¹ Bᴴ ∘ₗ (vecE a).symm.toLinearMap with haL
  have haL_apply : ∀ M, aL (vecE a M) = vecE a (heis K Ea (M * (Bᴴ)⁻¹) * Bᴴ) := fun M => by
    simp [haL, sandL]
  set Φ : EuclideanSpace ℂ (a × a) →ₗ[ℂ] EuclideanSpace ℂ (a × a) :=
    (vecE a).toLinearMap ∘ₗ (LinearMap.mulLeft ℂ B ∘ₗ LinearMap.mulRight ℂ (Bᴴ)⁻¹) ∘ₗ
      (vecE a).symm.toLinearMap with hΦdef
  have hΦ_apply : ∀ M, Φ (vecE a M) = vecE a (B * (M * (Bᴴ)⁻¹)) := fun M => by
    simp [hΦdef, Matrix.mul_assoc]
  set Gs : Submodule ℂ (EuclideanSpace ℂ (a × a)) :=
    LinearMap.range ((vecE a).toLinearMap ∘ₗ slcL ρ 1 (ω⁻¹ * Bᴴ)) with hGs
  have hG : ∀ Y', vecE a (slc ρ Y' * ω⁻¹ * Bᴴ) ∈ Gs := fun Y' =>
    ⟨Y', by simp [slcL, Matrix.mul_assoc]⟩
  have hmem : ∀ x ∈ Gs, ∃ Y', x = vecE a (slc ρ Y' * ω⁻¹ * Bᴴ) := by
    rintro x ⟨Y', rfl⟩
    exact ⟨Y', by simp [slcL, Matrix.mul_assoc]⟩
  have nB : ∀ W, ‖vecE a (W * Bᴴ)‖ ^ 2 = (ω * (Wᴴ * W)).trace.re := by
    intro W
    rw [norm_vecE, hB, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    congr 1
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have nB' : ∀ W, ‖vecE a (B * W)‖ ^ 2 = (ω * (W * Wᴴ)).trace.re := by
    intro W
    rw [norm_vecE, hB, Matrix.conjTranspose_mul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm Wᴴ]
    simp only [Matrix.mul_assoc]
  have hZB : ∀ Z : Matrix a a ℂ, Z * Bᴴ * (Bᴴ)⁻¹ = Z := fun Z => by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBHu, Matrix.mul_one]
  have haLZ : ∀ Z, aL (vecE a (Z * Bᴴ)) = vecE a (heis K Ea Z * Bᴴ) := by
    intro Z; rw [haL_apply, hZB]
  have hΦZ : ∀ Z, Φ (vecE a (Z * Bᴴ)) = vecE a (B * Z) := by
    intro Z; rw [hΦ_apply, hZB]
  have hTG : ∀ x ∈ Gs, aL x ∈ Gs := by
    intro x hx
    obtain ⟨Y', rfl⟩ := hmem x hx
    rw [haLZ, (hti Y').1]
    exact hG _
  have hTn : ∀ x ∈ Gs, ‖aL x‖ = ‖x‖ := by
    intro x hx
    obtain ⟨Y', rfl⟩ := hmem x hx
    rw [haLZ]
    have hint := (hti Y').2
    set Z := slc ρ Y' * ω⁻¹ with hZ
    have e : ∀ k, (K k)ᴴ * Ea (Zᴴ * Z) * K k =
        (heis K Ea Z)ᴴ * ((K k)ᴴ * K k) * heis K Ea Z := by
      intro k
      rw [← hEa, show (K k)ᴴ * ((Ea Z)ᴴ * Ea Z) * K k = (Ea Z * K k)ᴴ * (Ea Z * K k) by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc], hint k,
        Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    have hsq : (heis K Ea Z)ᴴ * heis K Ea Z = heis K Ea (Zᴴ * Z) := by
      conv_rhs => rw [heis]
      rw [Finset.sum_congr rfl fun k _ => e k, ← Finset.sum_mul, ← Finset.mul_sum, hK',
        Matrix.mul_one]
    have h2 : ‖vecE a (heis K Ea Z * Bᴴ)‖ ^ 2 = ‖vecE a (Z * Bᴴ)‖ ^ 2 := by
      rw [nB, nB, hsq, hinvA]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  let U : Gs →ₗᵢ[ℂ] Gs :=
    { toLinearMap := aL.restrict hTG
      norm_map' := fun y => by
        show ‖aL y‖ = ‖(y : EuclideanSpace ℂ (a × a))‖
        exact hTn y y.2 }
  let Ue : Gs ≃ₗᵢ[ℂ] Gs := U.toLinearIsometryEquiv rfl
  obtain ⟨Y', hY'⟩ := hmem _ (Ue.symm ⟨_, hG Y⟩).2
  have h1 : (U (Ue.symm ⟨_, hG Y⟩) : EuclideanSpace ℂ (a × a)) =
      vecE a (slc ρ Y * ω⁻¹ * Bᴴ) := by
    have := Ue.apply_symm_apply ⟨_, hG Y⟩
    exact congrArg Subtype.val this
  have h2 : (U (Ue.symm ⟨_, hG Y⟩) : EuclideanSpace ℂ (a × a)) =
      aL (Ue.symm ⟨_, hG Y⟩) := rfl
  rw [h2, hY', haLZ] at h1
  refine ⟨Y', ?_⟩
  have h3 := (vecE a).injective h1
  have h4 := congrArg (· * (Bᴴ)⁻¹) h3
  simp only [hZB] at h4
  exact h4

/-- Generalised Lindblad commutation: `K U' = (U ⊗ 1) K` and `K V' = (1 ⊗ V) K` force
`U' V' = V' U'`. -/
theorem C2gen {a : Type} [Fintype a] [DecidableEq a] {m : ℕ} (K : Fin m → Matrix (a × a) a ℂ)
    (U U' V V' : Matrix a a ℂ) (hK : QAlgorithms.IsKrausFamily K)
    (hU : ∀ k, K k * U' = (U ⊗ₖ (1 : Matrix a a ℂ)) * K k)
    (hV : ∀ k, K k * V' = ((1 : Matrix a a ℂ) ⊗ₖ V) * K k) : U' * V' = V' * U' := by
  have hK' : (∑ k, (K k)ᴴ * K k) = 1 := hK
  have hc : (U ⊗ₖ (1 : Matrix a a ℂ)) * ((1 : Matrix a a ℂ) ⊗ₖ V) =
      ((1 : Matrix a a ℂ) ⊗ₖ V) * (U ⊗ₖ (1 : Matrix a a ℂ)) := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.one_mul, Matrix.mul_one]
  calc U' * V' = (∑ k, (K k)ᴴ * K k) * (U' * V') := by rw [hK', Matrix.one_mul]
    _ = ∑ k, (K k)ᴴ * ((U ⊗ₖ (1 : Matrix a a ℂ)) * (((1 : Matrix a a ℂ) ⊗ₖ V) * K k)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (K k), hU, Matrix.mul_assoc, hV]
    _ = ∑ k, (K k)ᴴ * (((1 : Matrix a a ℂ) ⊗ₖ V) * ((U ⊗ₖ (1 : Matrix a a ℂ)) * K k)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Matrix.mul_assoc (U ⊗ₖ (1 : Matrix a a ℂ)), hc, Matrix.mul_assoc]
    _ = (∑ k, (K k)ᴴ * K k) * (V' * U') := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (K k), hV, Matrix.mul_assoc, hU]
    _ = V' * U' := by rw [hK', Matrix.one_mul]

/-- A normal `Z` with `Z ω` Hermitian (`ω` positive definite) is Hermitian. -/
lemma normal_herm {a : Type} [Fintype a] [DecidableEq a] (Z ω : Matrix a a ℂ)
    (hω : ω.PosSemidef) (hu : IsUnit ω.det) (hN : Z * Zᴴ = Zᴴ * Z) (hH : (Z * ω)ᴴ = Z * ω) :
    Zᴴ = Z := by
  have hZω : ω * Zᴴ = Z * ω := by
    have h := hH
    rw [Matrix.conjTranspose_mul, hω.1.eq] at h
    exact h
  have e : (Z - Zᴴ) * ω * (Z - Zᴴ)ᴴ =
      Z * (ω * Zᴴ) - Z * ω * Z - Zᴴ * (ω * Zᴴ) + Zᴴ * ω * Z := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
    noncomm_ring
  have t1 : (Z * ω * Z).trace = (Z * (Z * ω)).trace := Matrix.trace_mul_comm _ _
  have t2 : (Zᴴ * ω * Z).trace = (Zᴴ * (Z * ω)).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hN, Matrix.mul_assoc]
  have htr : ((Z - Zᴴ) * ω * (Z - Zᴴ)ᴴ).trace = 0 := by
    rw [e, hZω]
    simp only [Matrix.trace_add, Matrix.trace_sub, t1, t2]
    ring
  obtain ⟨B, hB⟩ := psd_factor ω hω
  have hBB : IsUnit (Bᴴ.det * B.det) := by
    have h := hu; rw [hB, Matrix.det_mul] at h; exact h
  have hBu : IsUnit B.det := isUnit_of_mul_isUnit_right hBB
  have h0 : ((B * (Z - Zᴴ)ᴴ)ᴴ * (B * (Z - Zᴴ)ᴴ)).trace = 0 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [hB] at htr
    simpa only [Matrix.mul_assoc] using htr
  have hBD := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp h0
  have hD : (Z - Zᴴ)ᴴ = 0 := by
    have h := congrArg (B⁻¹ * ·) hBD
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBu, Matrix.one_mul,
      Matrix.mul_zero] at h
    exact h
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose] at hD
  exact sub_eq_zero.1 hD

set_option maxHeartbeats 1000000 in
/-- R3 (A side, faithful marginals): a locally broadcastable state has commuting A-slices. -/
theorem sliceA_comm {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {m n : ℕ}
    (ρ : Matrix (a × b) (a × b) ℂ) (K : Fin m → Matrix (a × a) a ℂ) (L : Fin n → Matrix (b × b) b ℂ)
    (hK : QAlgorithms.IsKrausFamily K) (hL : QAlgorithms.IsKrausFamily L)
    (hcop : NoLocalBroadcast.Broadcast.traceCopies (NoLocalBroadcast.Broadcast.localApply K L ρ) = ρ)
    (horig : NoLocalBroadcast.Broadcast.traceOriginals
      (NoLocalBroadcast.Broadcast.localApply K L ρ) = ρ)
    (hρ : ρ.IsHermitian)
    (hωA : (QAlgorithms.traceRight ρ).PosSemidef) (hωB : (QAlgorithms.traceLeft ρ).PosSemidef)
    (huA : IsUnit (QAlgorithms.traceRight ρ).det) (huB : IsUnit (QAlgorithms.traceLeft ρ).det)
    (Y Y' : Matrix b b ℂ) : slc ρ Y * slc ρ Y' = slc ρ Y' * slc ρ Y := by
  have bR := bc_copies ρ K L hcop
  have bL := bc_originals ρ K L horig
  have tiR := fun Y => trace_inst ρ K L hK hL (kronR a) (kronR b) kronR_mul kronR_mul kronR_H
    kronR_one kronR_one bR hωA hωB huA huB Y
  have tiL := fun Y => trace_inst ρ K L hK hL (kronL a) (kronL b) kronL_mul kronL_mul kronL_H
    kronL_one kronL_one bL hωA hωB huA huB Y
  have adjL := fun Y => adj_inst ρ K L hK hL (kronL a) (kronL b) kronL_mul kronL_mul kronL_H
    kronL_one kronL_one bL hωA hωB huA huB Y
  have surjR := fun Y => surj_inst ρ K L hK hL (kronR a) (kronR b) kronR_mul kronR_mul kronR_H
    kronR_one kronR_one bR hωA hωB huA huB Y
  have surjL := fun Y => surj_inst ρ K L hK hL (kronL a) (kronL b) kronL_mul kronL_mul kronL_H
    kronL_one kronL_one bL hωA hωB huA huB Y
  have comm : ∀ U V : Matrix a a ℂ,
      (∀ k, kronR a U * K k = K k * heis K (kronR a) U) →
      (∀ k, kronL a V * K k = K k * heis K (kronL a) V) →
      heis K (kronR a) U * heis K (kronL a) V = heis K (kronL a) V * heis K (kronR a) U :=
    fun U V hU hV => C2gen K U _ V _ hK (fun k => by rw [← kronR_apply]; exact (hU k).symm)
      (fun k => by rw [← kronL_apply]; exact (hV k).symm)
  have hsH : ∀ Y : Matrix b b ℂ, Y.IsHermitian → (slc ρ Y)ᴴ = slc ρ Y :=
    fun Y hY => slice_isHermitian ρ hρ Y hY
  set ω := QAlgorithms.traceRight ρ with hωdef
  have hZω : ∀ Y, slc ρ Y * ω⁻¹ * ω = slc ρ Y := fun Y => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ huA, Matrix.mul_one]
  have herm : ∀ Y : Matrix b b ℂ, Y.IsHermitian → (slc ρ Y * ω⁻¹)ᴴ = slc ρ Y * ω⁻¹ := by
    intro Y hY
    obtain ⟨Y1, hY1⟩ := surjR Y
    obtain ⟨Y2, hY2⟩ := surjL Y
    have hZH : (slc ρ Y * ω⁻¹)ᴴ = heis K (kronL a) ((slc ρ Y2 * ω⁻¹)ᴴ) := by
      rw [← heis_conj K (kronL a) kronL_H, hY2]
    have hN : (slc ρ Y * ω⁻¹) * (slc ρ Y * ω⁻¹)ᴴ = (slc ρ Y * ω⁻¹)ᴴ * (slc ρ Y * ω⁻¹) := by
      have h := comm (slc ρ Y1 * ω⁻¹) ((slc ρ Y2 * ω⁻¹)ᴴ) ((tiR Y1).2) (adjL Y2)
      rw [hY1, ← hZH] at h
      exact h
    refine normal_herm _ ω hωA huA hN ?_
    rw [hZω]
    exact hsH Y hY
  have gcomm : ∀ Y1 Y2 : Matrix b b ℂ,
      (slc ρ Y1 * ω⁻¹) * (slc ρ Y2 * ω⁻¹) = (slc ρ Y2 * ω⁻¹) * (slc ρ Y1 * ω⁻¹) := by
    intro Y1 Y2
    obtain ⟨W1, h1⟩ := surjR Y1
    obtain ⟨W2, h2⟩ := surjL Y2
    have h := comm _ _ ((tiR W1).2) ((tiL W2).2)
    rw [h1, h2] at h
    exact h
  have hcω : ∀ Y : Matrix b b ℂ, Y.IsHermitian → ω * (slc ρ Y * ω⁻¹) = slc ρ Y * ω⁻¹ * ω := by
    intro Y hY
    have h1 := herm Y hY
    have hs := hsH Y hY
    rw [← hZω Y] at hs
    rw [Matrix.conjTranspose_mul, h1, hωA.1.eq] at hs
    exact hs
  have hcH : ∀ Y Y' : Matrix b b ℂ, Y.IsHermitian → Y'.IsHermitian →
      slc ρ Y * slc ρ Y' = slc ρ Y' * slc ρ Y := by
    intro Y Y' hY hY'
    have hc1 := hcω Y hY
    have hc2 := hcω Y' hY'
    have hg := gcomm Y Y'
    rw [← hZω Y, ← hZω Y']
    generalize slc ρ Y * ω⁻¹ = Z at hc1 hc2 hg ⊢
    generalize slc ρ Y' * ω⁻¹ = Z' at hc1 hc2 hg ⊢
    calc Z * ω * (Z' * ω) = Z * (ω * Z') * ω := by simp only [Matrix.mul_assoc]
      _ = Z * Z' * (ω * ω) := by rw [hc2]; simp only [Matrix.mul_assoc]
      _ = Z' * Z * (ω * ω) := by rw [hg]
      _ = Z' * (ω * Z) * ω := by rw [hc1]; simp only [Matrix.mul_assoc]
      _ = Z' * ω * (Z * ω) := by simp only [Matrix.mul_assoc]
  obtain ⟨H1, H2, h1, h2, rfl⟩ := herm_decomp Y
  obtain ⟨H1', H2', h1', h2', rfl⟩ := herm_decomp Y'
  have c11 := hcH H1 H1' h1 h1'
  have c12 := hcH H1 H2' h1 h2'
  have c21 := hcH H2 H1' h2 h1'
  have c22 := hcH H2 H2' h2 h2'
  simp only [slc_add, slc_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    c11, c12, c21, c22, smul_add]
  abel

/-! ### Swap of tensor factors (R4) -/

/-- Swap the tensor factors of an operator on `α × β`. -/
def sw {α β : Type} (M : Matrix (α × β) (α × β) ℂ) : Matrix (β × α) (β × α) ℂ :=
  M.submatrix Prod.swap Prod.swap

lemma kron_sw {α α₁ β β₁ : Type} (A : Matrix α₁ α ℂ) (B : Matrix β₁ β ℂ) :
    (A ⊗ₖ B).submatrix Prod.swap Prod.swap = B ⊗ₖ A := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [Matrix.kroneckerMap_apply, mul_comm]

lemma la_swap {a b : Type} [Fintype a] [Fintype b] {m n : ℕ}
    (K : Fin m → Matrix (a × a) a ℂ) (L : Fin n → Matrix (b × b) b ℂ)
    (ρ : Matrix (a × b) (a × b) ℂ) :
    NoLocalBroadcast.Broadcast.localApply L K (sw ρ) =
      sw (NoLocalBroadcast.Broadcast.localApply K L ρ) := by
  have hterm : ∀ k l, L l ⊗ₖ K k * sw ρ * (L l ⊗ₖ K k)ᴴ =
      (K k ⊗ₖ L l * ρ * (K k ⊗ₖ L l)ᴴ).submatrix Prod.swap Prod.swap := by
    intro k l
    rw [Matrix.submatrix_mul _ _ _ Prod.swap _ Prod.swap_bijective,
      Matrix.submatrix_mul _ _ _ Prod.swap _ Prod.swap_bijective, kron_sw,
      ← Matrix.conjTranspose_submatrix, kron_sw, sw]
  ext p q
  simp only [NoLocalBroadcast.Broadcast.localApply, QAlgorithms.krausApply, Matrix.sum_apply,
    Fintype.sum_prod_type, hterm]
  conv_rhs => rw [sw, Matrix.submatrix_apply, Matrix.sum_apply]
  simp only [Matrix.sum_apply, Matrix.submatrix_apply]
  exact Finset.sum_comm

lemma tc_swap {a b : Type} [Fintype a] [Fintype b]
    (σ : Matrix ((a × a) × (b × b)) ((a × a) × (b × b)) ℂ) :
    NoLocalBroadcast.Broadcast.traceCopies (sw σ) = sw (NoLocalBroadcast.Broadcast.traceCopies σ) := by
  ext p q
  simp only [NoLocalBroadcast.Broadcast.traceCopies, sw, Matrix.submatrix_apply, Matrix.of_apply,
    Prod.fst_swap, Prod.snd_swap]
  exact Finset.sum_comm

lemma to_swap {a b : Type} [Fintype a] [Fintype b]
    (σ : Matrix ((a × a) × (b × b)) ((a × a) × (b × b)) ℂ) :
    NoLocalBroadcast.Broadcast.traceOriginals (sw σ) =
      sw (NoLocalBroadcast.Broadcast.traceOriginals σ) := by
  ext p q
  simp only [NoLocalBroadcast.Broadcast.traceOriginals, sw, Matrix.submatrix_apply, Matrix.of_apply,
    Prod.fst_swap, Prod.snd_swap]
  exact Finset.sum_comm

lemma sw_sw {α β : Type} (M : Matrix (α × β) (α × β) ℂ) : sw (sw M) = M := by
  ext ⟨i, j⟩ ⟨k, l⟩; rfl

lemma trR_sw {a b : Type} [Fintype a] (ρ : Matrix (a × b) (a × b) ℂ) :
    QAlgorithms.traceRight (sw ρ) = QAlgorithms.traceLeft ρ := by
  ext j k; rfl

lemma trL_sw {a b : Type} [Fintype b] (ρ : Matrix (a × b) (a × b) ℂ) :
    QAlgorithms.traceLeft (sw ρ) = QAlgorithms.traceRight ρ := by
  ext j k; rfl

lemma herm_sw {a b : Type} (ρ : Matrix (a × b) (a × b) ℂ) (hρ : ρ.IsHermitian) :
    (sw ρ).IsHermitian := by
  rw [sw, Matrix.IsHermitian, Matrix.conjTranspose_submatrix, hρ.eq]

lemma slc_sw {a b : Type} [Fintype a] [Fintype b] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ) (X : Matrix a a ℂ) :
    QAlgorithms.traceRight (((1 : Matrix b b ℂ) ⊗ₖ X) * sw ρ) =
      QAlgorithms.traceLeft ((X ⊗ₖ (1 : Matrix b b ℂ)) * ρ) := by
  rw [← trR_sw, sw, sw, Matrix.submatrix_mul _ _ _ Prod.swap _ Prod.swap_bijective, kron_sw]


/-- R4 (B side, faithful marginals): a locally broadcastable state has commuting B-slices. -/
theorem sliceB_comm {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {m n : ℕ}
    (ρ : Matrix (a × b) (a × b) ℂ) (K : Fin m → Matrix (a × a) a ℂ) (L : Fin n → Matrix (b × b) b ℂ)
    (hK : QAlgorithms.IsKrausFamily K) (hL : QAlgorithms.IsKrausFamily L)
    (hcop : NoLocalBroadcast.Broadcast.traceCopies (NoLocalBroadcast.Broadcast.localApply K L ρ) = ρ)
    (horig : NoLocalBroadcast.Broadcast.traceOriginals
      (NoLocalBroadcast.Broadcast.localApply K L ρ) = ρ)
    (hρ : ρ.IsHermitian)
    (hωA : (QAlgorithms.traceRight ρ).PosSemidef) (hωB : (QAlgorithms.traceLeft ρ).PosSemidef)
    (huA : IsUnit (QAlgorithms.traceRight ρ).det) (huB : IsUnit (QAlgorithms.traceLeft ρ).det)
    (X X' : Matrix a a ℂ) :
    QAlgorithms.traceLeft ((X ⊗ₖ (1 : Matrix b b ℂ)) * ρ) *
        QAlgorithms.traceLeft ((X' ⊗ₖ (1 : Matrix b b ℂ)) * ρ) =
      QAlgorithms.traceLeft ((X' ⊗ₖ (1 : Matrix b b ℂ)) * ρ) *
        QAlgorithms.traceLeft ((X ⊗ₖ (1 : Matrix b b ℂ)) * ρ) := by
  have h := sliceA_comm (sw ρ) L K hL hK (by rw [la_swap, tc_swap, hcop])
    (by rw [la_swap, to_swap, horig]) (herm_sw ρ hρ) (by rw [trR_sw]; exact hωB)
    (by rw [trL_sw]; exact hωA) (by rw [trR_sw]; exact huB) (by rw [trL_sw]; exact huA) X X'
  simp only [slc, slc_sw] at h
  exact h

/-! ### R5: WLOG faithful marginals -/

/-- L1: a PSD matrix with zero weight on a projection is killed by it. -/
lemma proj_kill {n : Type} [Fintype n] [DecidableEq n] (M Q : Matrix n n ℂ) (hM : M.PosSemidef)
    (hQh : Qᴴ = Q) (hQQ : Q * Q = Q) (h0 : (Q * M).trace = 0) : Q * M = 0 := by
  obtain ⟨B, rfl⟩ := psd_factor M hM
  have h1 : ((B * Q)ᴴ * (B * Q)).trace = 0 := by
    calc ((B * Q)ᴴ * (B * Q)).trace = (Q * (Bᴴ * B) * Q).trace := by
          rw [Matrix.conjTranspose_mul, hQh]; simp only [Matrix.mul_assoc]
      _ = (Q * (Q * (Bᴴ * B))).trace := by rw [Matrix.trace_mul_comm]
      _ = (Q * (Bᴴ * B)).trace := by rw [← Matrix.mul_assoc, hQQ]
      _ = 0 := h0
  have h2 := (Matrix.posSemidef_conjTranspose_mul_self (B * Q)).trace_eq_zero_iff.1 h1
  have h3 : B * Q = 0 := Matrix.conjTranspose_mul_self_eq_zero.1 h2
  have h4 : (Bᴴ * B) * Q = 0 := by rw [Matrix.mul_assoc, h3, Matrix.mul_zero]
  have h5 := congrArg Matrix.conjTranspose h4
  simpa [Matrix.conjTranspose_mul, hQh] using h5

/-- L2: the support isometry of a PSD matrix. -/
lemma support_iso {a : Type} [Fintype a] [DecidableEq a] (ω : Matrix a a ℂ) (hω : ω.PosSemidef) :
    ∃ (r : Type) (_ : Fintype r) (_ : DecidableEq r) (V : Matrix a r ℂ) (D : Matrix r r ℂ),
      Vᴴ * V = 1 ∧ ω = V * D * Vᴴ ∧ IsUnit D.det := by
  set hH := hω.isHermitian
  set U : Matrix a a ℂ := (hH.eigenvectorUnitary : Matrix a a ℂ) with hU
  let r := {i : a // hH.eigenvalues i ≠ 0}
  refine ⟨r, inferInstance, inferInstance, U.submatrix id Subtype.val,
    Matrix.diagonal fun j : r => ((hH.eigenvalues j.val : ℝ) : ℂ), ?_, ?_, ?_⟩
  · have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
    ext i j
    have := congrFun (congrFun hUU i.val) j.val
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id,
      Matrix.star_apply] at this ⊢
    rw [this, Matrix.one_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg (fun h => hij (Subtype.ext h)), if_neg hij]
  · have hs := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hs
    have key : ∀ f : a → ℂ, (∀ i, hH.eigenvalues i = 0 → f i = 0) →
        ∑ j : r, f j.val = ∑ i, f i := by
      intro f hf
      rw [← Finset.sum_subtype (Finset.univ.filter fun i => hH.eigenvalues i ≠ 0)
        (by intro i; simp) f]
      exact Finset.sum_filter_of_ne fun i _ hne h0 => hne (hf i h0)
    ext x y
    have := congrFun (congrFun hs x) y
    rw [this]
    simp only [← hU, Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.conjTranspose_apply,
      Matrix.submatrix_apply, id, Matrix.star_apply, Function.comp_apply]
    exact (key (fun i => U x i * ((hH.eigenvalues i : ℝ) : ℂ) * star (U y i))
      (by intro i h; simp [h])).symm
  · rw [Matrix.det_diagonal]
    refine isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun j _ => ?_)
    exact_mod_cast j.2

/-- L3: equality of operators on `a × b` tested against product operators. -/
lemma ext_kron_trace {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (M M' : Matrix (a × b) (a × b) ℂ)
    (h : ∀ (Z : Matrix a a ℂ) (Y : Matrix b b ℂ), ((Z ⊗ₖ Y) * M).trace = ((Z ⊗ₖ Y) * M').trace) :
    M = M' := by
  ext ⟨i, j⟩ ⟨k, l⟩
  have := h (Matrix.single k i 1) (Matrix.single l j 1)
  simpa [Matrix.trace, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.single_apply,
    Fintype.sum_prod_type, ite_and] using this

/-- L3': equality of operators tested against all operators. -/
lemma ext_trace {a : Type} [Fintype a] [DecidableEq a] (M M' : Matrix a a ℂ)
    (h : ∀ Z : Matrix a a ℂ, (Z * M).trace = (Z * M').trace) : M = M' := by
  ext i k
  have := h (Matrix.single k i 1)
  simpa [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq,
    Finset.sum_ite_eq'] using this


lemma proj_fix {n : Type} [Fintype n] [DecidableEq n] (M P : Matrix n n ℂ) (hM : M.PosSemidef)
    (hPh : Pᴴ = P) (hPP : P * P = P) (htr : (P * M).trace = M.trace) : P * M = M := by
  have hQ := proj_kill M (1 - P) hM
    (by rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPh])
    (by simp only [sub_mul, mul_sub, one_mul, mul_one, hPP, sub_self, sub_zero])
    (by rw [sub_mul, one_mul, Matrix.trace_sub, htr, sub_self])
  rw [sub_mul, one_mul, sub_eq_zero] at hQ
  exact hQ.symm

lemma proj_of_iso {a r : Type} [Fintype a] [Fintype r] [DecidableEq r] (V : Matrix a r ℂ)
    (hV : Vᴴ * V = 1) : (V * Vᴴ)ᴴ = V * Vᴴ ∧ (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ :=
  ⟨by rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose],
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, hV, Matrix.one_mul]⟩

lemma trace_trR {a b : Type} [Fintype a] [Fintype b] (ρ : Matrix (a × b) (a × b) ℂ) :
    (QAlgorithms.traceRight ρ).trace = ρ.trace := by
  simp only [Matrix.trace, Matrix.diag, QAlgorithms.traceRight, Matrix.of_apply,
    Fintype.sum_prod_type]

lemma trace_trL {a b : Type} [Fintype a] [Fintype b] (ρ : Matrix (a × b) (a × b) ℂ) :
    (QAlgorithms.traceLeft ρ).trace = ρ.trace := by
  simp only [Matrix.trace, Matrix.diag, QAlgorithms.traceLeft, Matrix.of_apply,
    Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma fix_left {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : ρ.PosSemidef) (P : Matrix a a ℂ) (hPh : Pᴴ = P)
    (hPP : P * P = P) (hPω : P * QAlgorithms.traceRight ρ = QAlgorithms.traceRight ρ) :
    (P ⊗ₖ (1 : Matrix b b ℂ)) * ρ = ρ :=
  proj_fix ρ _ hρ (by rw [Matrix.conjTranspose_kronecker, hPh, Matrix.conjTranspose_one])
    (by rw [← Matrix.mul_kronecker_mul, hPP, Matrix.mul_one]) (by rw [t_trR, hPω, trace_trR])

lemma fix_right {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : ρ.PosSemidef) (P : Matrix b b ℂ) (hPh : Pᴴ = P)
    (hPP : P * P = P) (hPω : P * QAlgorithms.traceLeft ρ = QAlgorithms.traceLeft ρ) :
    ((1 : Matrix a a ℂ) ⊗ₖ P) * ρ = ρ :=
  proj_fix ρ _ hρ (by rw [Matrix.conjTranspose_kronecker, hPh, Matrix.conjTranspose_one])
    (by rw [← Matrix.mul_kronecker_mul, hPP, Matrix.mul_one]) (by rw [t_trL, hPω, trace_trL])

lemma fix_sigma_c {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (σ : Matrix ((a × a) × (b × b)) ((a × a) × (b × b)) ℂ) (ρ : Matrix (a × b) (a × b) ℂ)
    (hσ : σ.PosSemidef) (hcop : NoLocalBroadcast.Broadcast.traceCopies σ = ρ)
    (P : Matrix a a ℂ) (hPh : Pᴴ = P) (hPP : P * P = P)
    (hPρ : (P ⊗ₖ (1 : Matrix b b ℂ)) * ρ = ρ) :
    ((P ⊗ₖ (1 : Matrix a a ℂ)) ⊗ₖ ((1 : Matrix b b ℂ) ⊗ₖ (1 : Matrix b b ℂ))) * σ = σ := by
  refine proj_fix σ _ hσ ?_ ?_ ?_
  · simp only [Matrix.conjTranspose_kronecker, hPh, Matrix.conjTranspose_one]
  · simp only [← Matrix.mul_kronecker_mul, hPP, Matrix.mul_one]
  · have h1 := tr_copies σ (1 : Matrix a a ℂ) (1 : Matrix b b ℂ)
    simp only [Matrix.one_kronecker_one, Matrix.one_mul] at h1
    rw [tr_copies, hcop, hPρ, h1, hcop]

lemma fix_sigma_o {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (σ : Matrix ((a × a) × (b × b)) ((a × a) × (b × b)) ℂ) (ρ : Matrix (a × b) (a × b) ℂ)
    (hσ : σ.PosSemidef) (horig : NoLocalBroadcast.Broadcast.traceOriginals σ = ρ)
    (P : Matrix a a ℂ) (hPh : Pᴴ = P) (hPP : P * P = P)
    (hPρ : (P ⊗ₖ (1 : Matrix b b ℂ)) * ρ = ρ) :
    (((1 : Matrix a a ℂ) ⊗ₖ P) ⊗ₖ ((1 : Matrix b b ℂ) ⊗ₖ (1 : Matrix b b ℂ))) * σ = σ := by
  refine proj_fix σ _ hσ ?_ ?_ ?_
  · simp only [Matrix.conjTranspose_kronecker, hPh, Matrix.conjTranspose_one]
  · simp only [← Matrix.mul_kronecker_mul, hPP, Matrix.mul_one]
  · have h1 := tr_originals σ (1 : Matrix a a ℂ) (1 : Matrix b b ℂ)
    simp only [Matrix.one_kronecker_one, Matrix.one_mul] at h1
    rw [tr_originals, horig, hPρ, h1, horig]


/-- Kraus operators of a broadcast channel map the support of `ω_A` into `supp ⊗ supp`. -/
lemma kraus_supp {a b r : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype r] [DecidableEq r] {m n : ℕ}
    (ρ : Matrix (a × b) (a × b) ℂ) (K : Fin m → Matrix (a × a) a ℂ) (L : Fin n → Matrix (b × b) b ℂ)
    (hL : QAlgorithms.IsKrausFamily L) (hωp : (QAlgorithms.traceRight ρ).PosSemidef)
    (V : Matrix a r ℂ) (D : Matrix r r ℂ) (hV : Vᴴ * V = 1)
    (hω : QAlgorithms.traceRight ρ = V * D * Vᴴ) (hD : IsUnit D.det)
    (hσ : (((V * Vᴴ) ⊗ₖ (V * Vᴴ)) ⊗ₖ ((1 : Matrix b b ℂ) ⊗ₖ (1 : Matrix b b ℂ))) *
      NoLocalBroadcast.Broadcast.localApply K L ρ = NoLocalBroadcast.Broadcast.localApply K L ρ) :
    ∀ k, ((V * Vᴴ) ⊗ₖ (V * Vᴴ)) * K k * V = K k * V := by
  obtain ⟨hPh, hPP⟩ := proj_of_iso V hV
  have hσ' := hσ
  rw [Matrix.one_kronecker_one] at hσ'
  set P := V * Vᴴ with hPdef
  set Q2 : Matrix (a × a) (a × a) ℂ := 1 - P ⊗ₖ P with hQ2
  have hQh : Q2ᴴ = Q2 := by
    rw [hQ2, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_kronecker, hPh]
  have hQQ : Q2 * Q2 = Q2 := by
    rw [hQ2]
    simp only [sub_mul, mul_sub, one_mul, mul_one, ← Matrix.mul_kronecker_mul, hPP, sub_self,
      sub_zero]
  have htr0 : ((Q2 ⊗ₖ (1 : Matrix (b × b) (b × b) ℂ)) *
      NoLocalBroadcast.Broadcast.localApply K L ρ).trace = 0 := by
    have hk : Q2 ⊗ₖ (1 : Matrix (b × b) (b × b) ℂ) =
        1 - (P ⊗ₖ P) ⊗ₖ (1 : Matrix (b × b) (b × b) ℂ) := by
      refine eq_sub_of_add_eq ?_
      rw [← Matrix.add_kronecker, hQ2, sub_add_cancel, Matrix.one_kronecker_one]
    rw [hk, sub_mul, Matrix.one_mul, hσ', sub_self, Matrix.trace_zero]
  have hL1 : (∑ l, (L l)ᴴ * (1 : Matrix (b × b) (b × b) ℂ) * L l) = 1 := by
    simp only [Matrix.mul_one]; exact hL
  have h1 := tr_local K L Q2 (1 : Matrix (b × b) (b × b) ℂ) ρ
  rw [hL1, htr0, t_trR] at h1
  obtain ⟨C, hC⟩ := psd_factor _ hωp
  have hTk : ∀ k, ((C * (K k)ᴴ * Q2) * (C * (K k)ᴴ * Q2)ᴴ).trace =
      ((K k)ᴴ * Q2 * K k * QAlgorithms.traceRight ρ).trace := by
    intro k
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hQh]
    rw [show C * (K k)ᴴ * Q2 * (Q2 * (K k * Cᴴ)) = C * ((K k)ᴴ * Q2 * K k * Cᴴ) by
      simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc Q2 Q2, hQQ]]
    rw [Matrix.trace_mul_comm, hC]
    simp only [Matrix.mul_assoc]
  have hsum : ∑ k, ((C * (K k)ᴴ * Q2) * (C * (K k)ᴴ * Q2)ᴴ).trace = 0 := by
    simp only [hTk]
    rw [← Matrix.trace_sum, ← Finset.sum_mul]
    exact h1
  have hnn : ∀ k ∈ (Finset.univ : Finset (Fin m)),
      0 ≤ ((C * (K k)ᴴ * Q2) * (C * (K k)ᴴ * Q2)ᴴ).trace :=
    fun k _ => (Matrix.posSemidef_self_mul_conjTranspose _).trace_nonneg
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum
  intro k
  have hTz : C * (K k)ᴴ * Q2 = 0 := Matrix.self_mul_conjTranspose_eq_zero.1
    ((Matrix.posSemidef_self_mul_conjTranspose _).trace_eq_zero_iff.1 (hz k (Finset.mem_univ _)))
  have h2 : QAlgorithms.traceRight ρ * (K k)ᴴ * Q2 = 0 := by
    have : Cᴴ * (C * (K k)ᴴ * Q2) = 0 := by rw [hTz, Matrix.mul_zero]
    rw [hC]
    simpa only [Matrix.mul_assoc] using this
  have h3 : Q2 * K k * QAlgorithms.traceRight ρ = 0 := by
    have := congrArg Matrix.conjTranspose h2
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQh,
      Matrix.conjTranspose_conjTranspose, hωp.1.eq, Matrix.conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have hωV : QAlgorithms.traceRight ρ * V = V * D := by
    rw [hω, Matrix.mul_assoc (V * D), hV, Matrix.mul_one]
  have h4 : Q2 * K k * V * D = 0 := by
    rw [Matrix.mul_assoc (Q2 * K k), ← hωV, ← Matrix.mul_assoc, h3, Matrix.zero_mul]
  have h5 : Q2 * K k * V = 0 := by
    have := congrArg (· * D⁻¹) h4
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hD, Matrix.mul_one,
      Matrix.zero_mul] at this
    rw [Matrix.mul_assoc]; exact this
  rw [hQ2, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h5
  exact h5.symm


/-! ### R5b: restriction to the supports of the marginals -/

lemma trR_psd {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : ρ.PosSemidef) :
    (QAlgorithms.traceRight ρ).PosSemidef := by
  obtain ⟨B, rfl⟩ := psd_factor ρ hρ
  have : QAlgorithms.traceRight (Bᴴ * B) =
      ∑ h : b, (Matrix.of fun (p : a × b) (i : a) => B p (i, h))ᴴ *
        (Matrix.of fun (p : a × b) (i : a) => B p (i, h)) := by
    ext j k
    simp only [QAlgorithms.traceRight, Matrix.of_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.sum_apply]
  rw [this]
  exact Matrix.posSemidef_sum _ fun h _ => Matrix.posSemidef_conjTranspose_mul_self _

lemma trL_psd {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : ρ.PosSemidef) :
    (QAlgorithms.traceLeft ρ).PosSemidef := by
  rw [← trR_sw]
  exact trR_psd (sw ρ) (hρ.submatrix Prod.swap)

lemma kron_cancel {a r : Type} [Fintype a] [Fintype r] [DecidableEq r] (V : Matrix a r ℂ)
    (hV : Vᴴ * V = 1) (Z : Matrix r r ℂ) : Vᴴ * (V * Z * Vᴴ) * V = Z := by
  simp only [← Matrix.mul_assoc]
  rw [hV, Matrix.one_mul, Matrix.mul_assoc, hV, Matrix.mul_one]

lemma tr_conj2 {a b r s : Type} [Fintype a] [Fintype b] [Fintype r] [Fintype s]
    (V : Matrix a r ℂ) (W : Matrix b s ℂ) (A : Matrix a a ℂ) (B : Matrix b b ℂ)
    (ρ' : Matrix (r × s) (r × s) ℂ) :
    (((Vᴴ * A * V) ⊗ₖ (Wᴴ * B * W)) * ρ').trace =
      ((A ⊗ₖ B) * ((V ⊗ₖ W) * ρ' * (V ⊗ₖ W)ᴴ)).trace := by
  rw [Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul, ← Matrix.conjTranspose_kronecker]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm ((V ⊗ₖ W)ᴴ)]
  simp only [Matrix.mul_assoc]

lemma heis_restrict {a r : Type} [Fintype a] [DecidableEq a] [Fintype r] [DecidableEq r] {m : ℕ}
    (K : Fin m → Matrix (a × a) a ℂ) (V : Matrix a r ℂ)
    (E : Matrix a a ℂ →ₗ[ℂ] Matrix (a × a) (a × a) ℂ)
    (E' : Matrix r r ℂ →ₗ[ℂ] Matrix (r × r) (r × r) ℂ)
    (hE : ∀ Z, (V ⊗ₖ V) * E' Z * (V ⊗ₖ V)ᴴ = E (V * Z * Vᴴ) * ((V * Vᴴ) ⊗ₖ (V * Vᴴ)))
    (hK : ∀ k, ((V * Vᴴ) ⊗ₖ (V * Vᴴ)) * K k * V = K k * V) (Z : Matrix r r ℂ) :
    heis (fun k => (V ⊗ₖ V)ᴴ * K k * V) E' Z = Vᴴ * heis K E (V * Z * Vᴴ) * V := by
  simp only [heis, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  calc ((V ⊗ₖ V)ᴴ * K k * V)ᴴ * E' Z * ((V ⊗ₖ V)ᴴ * K k * V)
      = Vᴴ * (K k)ᴴ * ((V ⊗ₖ V) * E' Z * (V ⊗ₖ V)ᴴ) * (K k * V) := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = Vᴴ * (K k)ᴴ * E (V * Z * Vᴴ) * (((V * Vᴴ) ⊗ₖ (V * Vᴴ)) * K k * V) := by
        rw [hE]; simp only [Matrix.mul_assoc]
    _ = Vᴴ * ((K k)ᴴ * E (V * Z * Vᴴ) * K k) * V := by
        rw [hK]; simp only [Matrix.mul_assoc]

lemma hE_R {a r : Type} [Fintype a] [DecidableEq a] [Fintype r] [DecidableEq r]
    (V : Matrix a r ℂ) (hV : Vᴴ * V = 1) (Z : Matrix r r ℂ) :
    (V ⊗ₖ V) * kronR r Z * (V ⊗ₖ V)ᴴ = kronR a (V * Z * Vᴴ) * ((V * Vᴴ) ⊗ₖ (V * Vᴴ)) := by
  have h1 : V * Z * Vᴴ * (V * Vᴴ) = V * Z * Vᴴ := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc (V * Z) Vᴴ V, hV, Matrix.mul_one]
  simp only [kronR_apply, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul, h1]

lemma hE_L {a r : Type} [Fintype a] [DecidableEq a] [Fintype r] [DecidableEq r]
    (V : Matrix a r ℂ) (hV : Vᴴ * V = 1) (Z : Matrix r r ℂ) :
    (V ⊗ₖ V) * kronL r Z * (V ⊗ₖ V)ᴴ = kronL a (V * Z * Vᴴ) * ((V * Vᴴ) ⊗ₖ (V * Vᴴ)) := by
  have h1 : V * Z * Vᴴ * (V * Vᴴ) = V * Z * Vᴴ := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc (V * Z) Vᴴ V, hV, Matrix.mul_one]
  simp only [kronL_apply, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul, h1]

lemma kraus_restrict {a r : Type} [Fintype a] [DecidableEq a] [Fintype r] [DecidableEq r] {m : ℕ}
    (K : Fin m → Matrix (a × a) a ℂ) (hK : QAlgorithms.IsKrausFamily K) (V : Matrix a r ℂ)
    (hV : Vᴴ * V = 1) (hKV : ∀ k, ((V * Vᴴ) ⊗ₖ (V * Vᴴ)) * K k * V = K k * V) :
    QAlgorithms.IsKrausFamily (fun k => (V ⊗ₖ V)ᴴ * K k * V) := by
  unfold QAlgorithms.IsKrausFamily at hK ⊢
  have h : ∀ k, ((V ⊗ₖ V)ᴴ * K k * V)ᴴ * ((V ⊗ₖ V)ᴴ * K k * V) = Vᴴ * ((K k)ᴴ * K k) * V := by
    intro k
    calc ((V ⊗ₖ V)ᴴ * K k * V)ᴴ * ((V ⊗ₖ V)ᴴ * K k * V)
        = Vᴴ * (K k)ᴴ * (((V * Vᴴ) ⊗ₖ (V * Vᴴ)) * K k * V) := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
            Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul, Matrix.mul_assoc]
      _ = Vᴴ * ((K k)ᴴ * K k) * V := by rw [hKV]; simp only [Matrix.mul_assoc]
  rw [Finset.sum_congr rfl fun k _ => h k, ← Matrix.sum_mul, ← Matrix.mul_sum, hK,
    Matrix.mul_one, hV]

lemma rho_restrict {a b r s : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s] (ρ : Matrix (a × b) (a × b) ℂ)
    (hρ : ρ.PosSemidef) (V : Matrix a r ℂ) (W : Matrix b s ℂ) (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1)
    (hPA : V * Vᴴ * QAlgorithms.traceRight ρ = QAlgorithms.traceRight ρ)
    (hPB : W * Wᴴ * QAlgorithms.traceLeft ρ = QAlgorithms.traceLeft ρ) :
    ρ = (V ⊗ₖ W) * ((V ⊗ₖ W)ᴴ * ρ * (V ⊗ₖ W)) * (V ⊗ₖ W)ᴴ := by
  obtain ⟨hPh, hPP⟩ := proj_of_iso V hV
  obtain ⟨hQh, hQQ⟩ := proj_of_iso W hW
  have h1 := fix_left ρ hρ _ hPh hPP hPA
  have h2 := fix_right ρ hρ _ hQh hQQ hPB
  have hX : (V ⊗ₖ W) * (V ⊗ₖ W)ᴴ =
      ((V * Vᴴ) ⊗ₖ (1 : Matrix b b ℂ)) * ((1 : Matrix a a ℂ) ⊗ₖ (W * Wᴴ)) := by
    simp only [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      Matrix.one_mul]
  have hL : (V ⊗ₖ W) * (V ⊗ₖ W)ᴴ * ρ = ρ := by rw [hX, Matrix.mul_assoc, h2, h1]
  have hR : ρ * ((V ⊗ₖ W) * (V ⊗ₖ W)ᴴ) = ρ := by
    have := congrArg Matrix.conjTranspose hL
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hρ.1.eq] at this
    exact this
  calc ρ = (V ⊗ₖ W) * (V ⊗ₖ W)ᴴ * ρ * ((V ⊗ₖ W) * (V ⊗ₖ W)ᴴ) := by rw [hL, hR]
    _ = _ := by simp only [Matrix.mul_assoc]

lemma trR_restrict {a b r s : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s] (ρ : Matrix (a × b) (a × b) ℂ)
    (V : Matrix a r ℂ) (W : Matrix b s ℂ) (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1)
    (ρ' : Matrix (r × s) (r × s) ℂ) (hρ' : ρ = (V ⊗ₖ W) * ρ' * (V ⊗ₖ W)ᴴ) :
    QAlgorithms.traceRight ρ' = Vᴴ * QAlgorithms.traceRight ρ * V := by
  refine ext_trace _ _ fun Z => ?_
  have hW1 : Wᴴ * (1 : Matrix b b ℂ) * W = 1 := by rw [Matrix.mul_one, hW]
  calc (Z * QAlgorithms.traceRight ρ').trace = ((Z ⊗ₖ (1 : Matrix s s ℂ)) * ρ').trace :=
        (t_trR _ _).symm
    _ = (((Vᴴ * (V * Z * Vᴴ) * V) ⊗ₖ (Wᴴ * (1 : Matrix b b ℂ) * W)) * ρ').trace := by
        rw [kron_cancel V hV, hW1]
    _ = (((V * Z * Vᴴ) ⊗ₖ (1 : Matrix b b ℂ)) * ρ).trace := by rw [tr_conj2, ← hρ']
    _ = (V * Z * Vᴴ * QAlgorithms.traceRight ρ).trace := t_trR _ _
    _ = (Z * (Vᴴ * QAlgorithms.traceRight ρ * V)).trace := by
        rw [show V * Z * Vᴴ * QAlgorithms.traceRight ρ =
          V * (Z * (Vᴴ * QAlgorithms.traceRight ρ)) by simp only [Matrix.mul_assoc],
          Matrix.trace_mul_comm V]
        simp only [Matrix.mul_assoc]

lemma trL_restrict {a b r s : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s] (ρ : Matrix (a × b) (a × b) ℂ)
    (V : Matrix a r ℂ) (W : Matrix b s ℂ) (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1)
    (ρ' : Matrix (r × s) (r × s) ℂ) (hρ' : ρ = (V ⊗ₖ W) * ρ' * (V ⊗ₖ W)ᴴ) :
    QAlgorithms.traceLeft ρ' = Wᴴ * QAlgorithms.traceLeft ρ * W := by
  refine ext_trace _ _ fun Z => ?_
  have hV1 : Vᴴ * (1 : Matrix a a ℂ) * V = 1 := by rw [Matrix.mul_one, hV]
  calc (Z * QAlgorithms.traceLeft ρ').trace = (((1 : Matrix r r ℂ) ⊗ₖ Z) * ρ').trace :=
        (t_trL _ _).symm
    _ = (((Vᴴ * (1 : Matrix a a ℂ) * V) ⊗ₖ (Wᴴ * (W * Z * Wᴴ) * W)) * ρ').trace := by
        rw [kron_cancel W hW, hV1]
    _ = (((1 : Matrix a a ℂ) ⊗ₖ (W * Z * Wᴴ)) * ρ).trace := by rw [tr_conj2, ← hρ']
    _ = (W * Z * Wᴴ * QAlgorithms.traceLeft ρ).trace := t_trL _ _
    _ = (Z * (Wᴴ * QAlgorithms.traceLeft ρ * W)).trace := by
        rw [show W * Z * Wᴴ * QAlgorithms.traceLeft ρ =
          W * (Z * (Wᴴ * QAlgorithms.traceLeft ρ)) by simp only [Matrix.mul_assoc],
          Matrix.trace_mul_comm W]
        simp only [Matrix.mul_assoc]

theorem bc_restrict {a b r s : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s] {m n : ℕ}
    (ρ : Matrix (a × b) (a × b) ℂ) (K : Fin m → Matrix (a × a) a ℂ)
    (L : Fin n → Matrix (b × b) b ℂ)
    (hcop : NoLocalBroadcast.Broadcast.traceCopies (NoLocalBroadcast.Broadcast.localApply K L ρ) = ρ)
    (horig : NoLocalBroadcast.Broadcast.traceOriginals
      (NoLocalBroadcast.Broadcast.localApply K L ρ) = ρ)
    (V : Matrix a r ℂ) (W : Matrix b s ℂ) (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1)
    (hKV : ∀ k, ((V * Vᴴ) ⊗ₖ (V * Vᴴ)) * K k * V = K k * V)
    (hLW : ∀ l, ((W * Wᴴ) ⊗ₖ (W * Wᴴ)) * L l * W = L l * W)
    (ρ' : Matrix (r × s) (r × s) ℂ) (hρ' : ρ = (V ⊗ₖ W) * ρ' * (V ⊗ₖ W)ᴴ) :
    NoLocalBroadcast.Broadcast.traceCopies (NoLocalBroadcast.Broadcast.localApply
      (fun k => (V ⊗ₖ V)ᴴ * K k * V) (fun l => (W ⊗ₖ W)ᴴ * L l * W) ρ') = ρ' ∧
    NoLocalBroadcast.Broadcast.traceOriginals (NoLocalBroadcast.Broadcast.localApply
      (fun k => (V ⊗ₖ V)ᴴ * K k * V) (fun l => (W ⊗ₖ W)ᴴ * L l * W) ρ') = ρ' := by
  have hc := bc_copies ρ K L hcop
  have ho := bc_originals ρ K L horig
  constructor
  · refine ext_kron_trace _ _ fun Z Y => ?_
    rw [← tr_copies, ← tr_local]
    calc ((heis (fun k => (V ⊗ₖ V)ᴴ * K k * V) (kronR r) Z ⊗ₖ
            heis (fun l => (W ⊗ₖ W)ᴴ * L l * W) (kronR s) Y) * ρ').trace
        = (((Vᴴ * heis K (kronR a) (V * Z * Vᴴ) * V) ⊗ₖ
            (Wᴴ * heis L (kronR b) (W * Y * Wᴴ) * W)) * ρ').trace := by
          rw [heis_restrict K V (kronR a) (kronR r) (hE_R V hV) hKV,
            heis_restrict L W (kronR b) (kronR s) (hE_R W hW) hLW]
      _ = (((V * Z * Vᴴ) ⊗ₖ (W * Y * Wᴴ)) * ρ).trace := by rw [tr_conj2, ← hρ', hc]
      _ = ((Z ⊗ₖ Y) * ρ').trace := by
          rw [hρ', ← tr_conj2, kron_cancel V hV, kron_cancel W hW]
  · refine ext_kron_trace _ _ fun Z Y => ?_
    rw [← tr_originals, ← tr_local]
    calc ((heis (fun k => (V ⊗ₖ V)ᴴ * K k * V) (kronL r) Z ⊗ₖ
            heis (fun l => (W ⊗ₖ W)ᴴ * L l * W) (kronL s) Y) * ρ').trace
        = (((Vᴴ * heis K (kronL a) (V * Z * Vᴴ) * V) ⊗ₖ
            (Wᴴ * heis L (kronL b) (W * Y * Wᴴ) * W)) * ρ').trace := by
          rw [heis_restrict K V (kronL a) (kronL r) (hE_L V hV) hKV,
            heis_restrict L W (kronL b) (kronL s) (hE_L W hW) hLW]
      _ = (((V * Z * Vᴴ) ⊗ₖ (W * Y * Wᴴ)) * ρ).trace := by rw [tr_conj2, ← hρ', ho]
      _ = ((Z ⊗ₖ Y) * ρ').trace := by
          rw [hρ', ← tr_conj2, kron_cancel V hV, kron_cancel W hW]

lemma inner_iso {a r : Type} [Fintype a] [Fintype r] [DecidableEq r] (V : Matrix a r ℂ)
    (hV : Vᴴ * V = 1) (x y : EuclideanSpace ℂ r) :
    ⟪(WithLp.toLp 2 (V *ᵥ WithLp.ofLp x) : EuclideanSpace ℂ a),
      (WithLp.toLp 2 (V *ᵥ WithLp.ofLp y) : EuclideanSpace ℂ a)⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [WithLp.ofLp_toLp]
  rw [Matrix.star_mulVec, dotProduct_comm (V *ᵥ _), Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, hV, Matrix.vecMul_one, dotProduct_comm]

lemma pure_iso {a r : Type} [Fintype a] [Fintype r] (V : Matrix a r ℂ) (x : EuclideanSpace ℂ r) :
    QAlgorithms.pureDensity (WithLp.toLp 2 (V *ᵥ WithLp.ofLp x) : EuclideanSpace ℂ a) =
      V * QAlgorithms.pureDensity x * Vᴴ := by
  ext i j
  simp only [QAlgorithms.pureDensity, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, PiLp.toLp_apply, Matrix.mulVec, dotProduct, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum, Complex.star_def]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem cc_transfer {a b r s : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s] (V : Matrix a r ℂ) (W : Matrix b s ℂ)
    (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1) (ρ' : Matrix (r × s) (r × s) ℂ)
    (h : NoLocalBroadcast.Broadcast.IsClassicalClassical ρ') :
    NoLocalBroadcast.Broadcast.IsClassicalClassical ((V ⊗ₖ W) * ρ' * (V ⊗ₖ W)ᴴ) := by
  obtain ⟨k, l, e, f, p, he, hf, hp0, hp1, hρ⟩ := h
  refine ⟨k, l, fun i => WithLp.toLp 2 (V *ᵥ WithLp.ofLp (e i)),
    fun j => WithLp.toLp 2 (W *ᵥ WithLp.ofLp (f j)), p, ?_, ?_, hp0, hp1, ?_⟩
  · rw [orthonormal_iff_ite] at he ⊢
    intro i j
    rw [inner_iso V hV]
    exact he i j
  · rw [orthonormal_iff_ite] at hf ⊢
    intro i j
    rw [inner_iso W hW]
    exact hf i j
  · rw [hρ, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun ij _ => ?_
    simp only [pure_iso, Matrix.mul_smul, Matrix.smul_mul, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul]

set_option maxHeartbeats 1000000 in
/-- C4: a locally broadcastable state is classical-classical. -/
theorem C4 {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ)
    (hb : NoLocalBroadcast.Broadcast.IsLocallyBroadcastable ρ) :
    NoLocalBroadcast.Broadcast.IsClassicalClassical ρ := by
  obtain ⟨m, n, K, L, hK, hL, hσ, hcop, horig⟩ := hb
  have hωA := trR_psd ρ hρ.1
  have hωB := trL_psd ρ hρ.1
  obtain ⟨r, _, _, V, D, hV, hωV, hD⟩ := support_iso _ hωA
  obtain ⟨s, _, _, W, E, hW, hωW, hE⟩ := support_iso _ hωB
  obtain ⟨hPh, hPP⟩ := proj_of_iso V hV
  obtain ⟨hQh, hQQ⟩ := proj_of_iso W hW
  have hPA : V * Vᴴ * QAlgorithms.traceRight ρ = QAlgorithms.traceRight ρ := by
    rw [hωV]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul]
  have hPB : W * Wᴴ * QAlgorithms.traceLeft ρ = QAlgorithms.traceLeft ρ := by
    rw [hωW]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc Wᴴ W, hW, Matrix.one_mul]
  -- A side: Kraus operators preserve the support
  have h1 := fix_left ρ hρ.1 _ hPh hPP hPA
  have hc := fix_sigma_c _ ρ hσ.1 hcop _ hPh hPP h1
  have ho := fix_sigma_o _ ρ hσ.1 horig _ hPh hPP h1
  have hsplit : ∀ (P : Matrix a a ℂ),
      ((P ⊗ₖ P) ⊗ₖ ((1 : Matrix b b ℂ) ⊗ₖ (1 : Matrix b b ℂ))) =
        ((P ⊗ₖ (1 : Matrix a a ℂ)) ⊗ₖ ((1 : Matrix b b ℂ) ⊗ₖ (1 : Matrix b b ℂ))) *
        (((1 : Matrix a a ℂ) ⊗ₖ P) ⊗ₖ ((1 : Matrix b b ℂ) ⊗ₖ (1 : Matrix b b ℂ))) := by
    intro P
    simp only [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have hKV := kraus_supp ρ K L hL hωA V D hV hωV hD
    (by rw [hsplit, Matrix.mul_assoc, ho, hc])
  -- B side via the swap
  have hsw : (sw ρ).PosSemidef := hρ.1.submatrix Prod.swap
  have hσsw : (NoLocalBroadcast.Broadcast.localApply L K (sw ρ)).PosSemidef := by
    rw [la_swap]; exact hσ.1.submatrix Prod.swap
  have hcop' : NoLocalBroadcast.Broadcast.traceCopies
      (NoLocalBroadcast.Broadcast.localApply L K (sw ρ)) = sw ρ := by rw [la_swap, tc_swap, hcop]
  have horig' : NoLocalBroadcast.Broadcast.traceOriginals
      (NoLocalBroadcast.Broadcast.localApply L K (sw ρ)) = sw ρ := by rw [la_swap, to_swap, horig]
  have hPB' : W * Wᴴ * QAlgorithms.traceRight (sw ρ) = QAlgorithms.traceRight (sw ρ) := by
    rw [trR_sw]; exact hPB
  have h1' := fix_left (sw ρ) hsw _ hQh hQQ hPB'
  have hc' := fix_sigma_c _ (sw ρ) hσsw hcop' _ hQh hQQ h1'
  have ho' := fix_sigma_o _ (sw ρ) hσsw horig' _ hQh hQQ h1'
  have hsplit' : ∀ (P : Matrix b b ℂ),
      ((P ⊗ₖ P) ⊗ₖ ((1 : Matrix a a ℂ) ⊗ₖ (1 : Matrix a a ℂ))) =
        ((P ⊗ₖ (1 : Matrix b b ℂ)) ⊗ₖ ((1 : Matrix a a ℂ) ⊗ₖ (1 : Matrix a a ℂ))) *
        (((1 : Matrix b b ℂ) ⊗ₖ P) ⊗ₖ ((1 : Matrix a a ℂ) ⊗ₖ (1 : Matrix a a ℂ))) := by
    intro P
    simp only [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have hLW := kraus_supp (sw ρ) L K hK (by rw [trR_sw]; exact hωB) W E hW
    (by rw [trR_sw]; exact hωW) hE (by rw [hsplit', Matrix.mul_assoc, ho', hc'])
  -- the restricted state
  have hρ' := rho_restrict ρ hρ.1 V W hV hW hPA hPB
  set ρ' := (V ⊗ₖ W)ᴴ * ρ * (V ⊗ₖ W) with hρ'def
  have hK' := kraus_restrict K hK V hV hKV
  have hL' := kraus_restrict L hL W hW hLW
  obtain ⟨bc1, bc2⟩ := bc_restrict ρ K L hcop horig V W hV hW hKV hLW ρ' hρ'
  have hρ'p : ρ'.PosSemidef := hρ.1.conjTranspose_mul_mul_same _
  have htrA : QAlgorithms.traceRight ρ' = D := by
    rw [trR_restrict ρ V W hV hW ρ' hρ', hωV, kron_cancel V hV]
  have htrB : QAlgorithms.traceLeft ρ' = E := by
    rw [trL_restrict ρ V W hV hW ρ' hρ', hωW, kron_cancel W hW]
  have hωA' : (QAlgorithms.traceRight ρ').PosSemidef := trR_psd ρ' hρ'p
  have hωB' : (QAlgorithms.traceLeft ρ').PosSemidef := trL_psd ρ' hρ'p
  have hρ'd : QAlgorithms.IsDensityMatrix ρ' := by
    refine ⟨hρ'p, ?_⟩
    rw [← trace_trR ρ', htrA, ← hρ.2, ← trace_trR ρ, hωV, Matrix.trace_mul_comm (V * D) Vᴴ,
      ← Matrix.mul_assoc, hV, Matrix.one_mul]
  have hA := sliceA_comm ρ' _ _ hK' hL' bc1 bc2 hρ'p.1 hωA' hωB'
    (by rw [htrA]; exact hD) (by rw [htrB]; exact hE)
  have hB := sliceB_comm ρ' _ _ hK' hL' bc1 bc2 hρ'p.1 hωA' hωB'
    (by rw [htrA]; exact hD) (by rw [htrB]; exact hE)
  have hcc := C3 ρ' hρ'd (fun Y Y' => hA Y Y') hB
  rw [hρ']
  exact cc_transfer V W hV hW ρ' hcc

/-- the column matrix of an orthonormal family is an isometry -/
lemma colV_iso {a : Type} [Fintype a] {k : ℕ} (e : Fin k → EuclideanSpace ℂ a)
    (he : Orthonormal ℂ e) :
    (Matrix.of fun x i => e i x)ᴴ * (Matrix.of fun x i => e i x) = 1 := by
  rw [orthonormal_iff_ite] at he
  ext i j
  have := he i j
  rw [EuclideanSpace.inner_eq_star_dotProduct] at this
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [← this]
  simp [dotProduct, mul_comm]

lemma sandw_single {m : Type} {k : ℕ} (C : Matrix m (Fin k) ℂ) (i : Fin k) (p q : m) :
    (C * (Matrix.single i i (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ) * Cᴴ) p q = C p i * star (C q i) := by
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply,
    ite_and, Finset.sum_ite_eq, ite_mul]

lemma pd_colV {a : Type} [Fintype a] {k : ℕ} (e : Fin k → EuclideanSpace ℂ a) (i : Fin k) :
    QAlgorithms.pureDensity (e i) =
      (Matrix.of fun x i => e i x) * (Matrix.single i i (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ) *
        (Matrix.of fun x i => e i x)ᴴ := by
  ext x y
  simp [QAlgorithms.pureDensity, Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply,
    ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul]

lemma pd_trace {a : Type} [Fintype a] {k : ℕ} (e : Fin k → EuclideanSpace ℂ a)
    (he : Orthonormal ℂ e) (i : Fin k) : (QAlgorithms.pureDensity (e i)).trace = 1 := by
  rw [orthonormal_iff_ite] at he
  have := he i i
  rw [EuclideanSpace.inner_eq_star_dotProduct] at this
  simp only [if_true] at this
  rw [← this]
  simp [QAlgorithms.pureDensity, Matrix.trace, dotProduct]

set_option maxHeartbeats 1000000 in
/-- the copier Kraus family for an orthonormal family -/
theorem copier {a : Type} [Fintype a] [DecidableEq a] [Nonempty a] {k : ℕ}
    (e : Fin k → EuclideanSpace ℂ a) (he : Orthonormal ℂ e) :
    ∃ K : Fin 2 → Matrix (a × a) a ℂ, QAlgorithms.IsKrausFamily K ∧
      ∀ i, QAlgorithms.krausApply K (QAlgorithms.pureDensity (e i)) =
        QAlgorithms.pureDensity (e i) ⊗ₖ QAlgorithms.pureDensity (e i) := by
  classical
  obtain ⟨z0⟩ := (inferInstance : Nonempty a)
  set V : Matrix a (Fin k) ℂ := Matrix.of fun x i => e i x with hVdef
  have hV : Vᴴ * V = 1 := colV_iso e he
  let C : Matrix (Fin k × Fin k) (Fin k) ℂ := Matrix.of fun p i => if p.1 = i ∧ p.2 = i then 1 else 0
  let J : Matrix (a × a) a ℂ := Matrix.of fun p w => if p.1 = w ∧ p.2 = z0 then 1 else 0
  have hC : Cᴴ * C = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [C, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_prod_type,
        ite_and]
    simp [hij, Ne.symm hij, C, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_prod_type,
      ite_and]
  have hJ : Jᴴ * J = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [J, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_prod_type,
        ite_and]
    simp [hij, Ne.symm hij, J, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_prod_type,
      ite_and]
  have hCE : ∀ i, C * (Matrix.single i i (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ) * Cᴴ =
      (Matrix.single i i (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ) ⊗ₖ
        (Matrix.single i i (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ) := by
    intro i
    ext ⟨x, x'⟩ ⟨y, y'⟩
    rw [sandw_single]
    simp only [C, Matrix.of_apply, Matrix.single_apply, Matrix.kroneckerMap_apply]
    split_ifs <;> (try simp_all) <;> grind
  let P : Matrix a a ℂ := V * Vᴴ
  have hPP : P * P = P := by
    simp only [P, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul]
  have hPH : Pᴴ = P := by simp [P, Matrix.conjTranspose_mul]
  let K0 : Matrix (a × a) a ℂ := (V ⊗ₖ V) * C * Vᴴ
  let K1 : Matrix (a × a) a ℂ := J * (1 - P)
  refine ⟨![K0, K1], ?_, ?_⟩
  · unfold QAlgorithms.IsKrausFamily
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    have h0 : K0ᴴ * K0 = P := by
      simp only [K0, P, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.conjTranspose_kronecker, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Vᴴ ⊗ₖ Vᴴ), ← Matrix.mul_kronecker_mul, hV, Matrix.one_kronecker_one,
        Matrix.one_mul, ← Matrix.mul_assoc Cᴴ, hC, Matrix.one_mul]
    have h1 : K1ᴴ * K1 = 1 - P := by
      simp only [K1, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Jᴴ, hJ, Matrix.one_mul, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_one, hPH, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hPP,
        Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
      abel
    rw [h0, h1]
    abel
  · intro i
    unfold QAlgorithms.krausApply
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    have hk1 : K1 * QAlgorithms.pureDensity (e i) = 0 := by
      rw [pd_colV e i]
      simp only [K1, P, Matrix.mul_assoc]
      rw [← hVdef, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc V, ← Matrix.mul_assoc Vᴴ V, hV,
        Matrix.one_mul, sub_self]
      simp
    rw [hk1, Matrix.zero_mul, add_zero, pd_colV e i, ← hVdef]
    have hK0 : K0 * (V * (Matrix.single i i (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ) * Vᴴ) * K0ᴴ =
        (V ⊗ₖ V) * (C * (Matrix.single i i (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ) * Cᴴ) * (V ⊗ₖ V)ᴴ := by
      simp only [K0, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul, ← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul]
    rw [hK0, hCE, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul]

lemma la_kron {a a₁ b b₁ : Type} [Fintype a] [Fintype b] {m n : ℕ}
    (K : Fin m → Matrix a₁ a ℂ) (L : Fin n → Matrix b₁ b ℂ) (X : Matrix a a ℂ) (Y : Matrix b b ℂ) :
    NoLocalBroadcast.Broadcast.localApply K L (X ⊗ₖ Y) =
      QAlgorithms.krausApply K X ⊗ₖ QAlgorithms.krausApply L Y := by
  unfold NoLocalBroadcast.Broadcast.localApply QAlgorithms.krausApply
  rw [Fintype.sum_prod_type, sum_kron]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [kron_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

lemma la_sum {a a₁ b b₁ ι : Type} [Fintype a] [Fintype b] [Fintype ι] {m n : ℕ}
    (K : Fin m → Matrix a₁ a ℂ) (L : Fin n → Matrix b₁ b ℂ) (c : ι → ℂ)
    (M : ι → Matrix (a × b) (a × b) ℂ) :
    NoLocalBroadcast.Broadcast.localApply K L (∑ i, c i • M i) =
      ∑ i, c i • NoLocalBroadcast.Broadcast.localApply K L (M i) := by
  unfold NoLocalBroadcast.Broadcast.localApply QAlgorithms.krausApply
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]
  rw [Finset.sum_comm]

lemma kraus_psd {ι κ J : Type} [Fintype ι] [Fintype κ] [Fintype J] (E : J → Matrix κ ι ℂ)
    (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) : (QAlgorithms.krausApply E ρ).PosSemidef := by
  unfold QAlgorithms.krausApply
  exact Matrix.posSemidef_sum _ fun j _ => hρ.mul_mul_conjTranspose_same (E j)

lemma tc_kron {a b : Type} [Fintype a] [Fintype b] (X X' : Matrix a a ℂ) (Y Y' : Matrix b b ℂ) :
    NoLocalBroadcast.Broadcast.traceCopies ((X ⊗ₖ X') ⊗ₖ (Y ⊗ₖ Y')) =
      (X'.trace * Y'.trace) • (X ⊗ₖ Y) := by
  ext p q
  simp only [NoLocalBroadcast.Broadcast.traceCopies, Matrix.of_apply, Matrix.kroneckerMap_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag]
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun y _ => by ring

lemma to_kron {a b : Type} [Fintype a] [Fintype b] (X X' : Matrix a a ℂ) (Y Y' : Matrix b b ℂ) :
    NoLocalBroadcast.Broadcast.traceOriginals ((X ⊗ₖ X') ⊗ₖ (Y ⊗ₖ Y')) =
      (X.trace * Y.trace) • (X' ⊗ₖ Y') := by
  ext p q
  simp only [NoLocalBroadcast.Broadcast.traceOriginals, Matrix.of_apply, Matrix.kroneckerMap_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag]
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun y _ => by ring

lemma tc_sum {a b ι : Type} [Fintype a] [Fintype b] [Fintype ι] (c : ι → ℂ)
    (M : ι → Matrix ((a × a) × (b × b)) ((a × a) × (b × b)) ℂ) :
    NoLocalBroadcast.Broadcast.traceCopies (∑ i, c i • M i) =
      ∑ i, c i • NoLocalBroadcast.Broadcast.traceCopies (M i) := by
  ext p q
  simp only [NoLocalBroadcast.Broadcast.traceCopies, Matrix.of_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  symm
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm)

lemma to_sum {a b ι : Type} [Fintype a] [Fintype b] [Fintype ι] (c : ι → ℂ)
    (M : ι → Matrix ((a × a) × (b × b)) ((a × a) × (b × b)) ℂ) :
    NoLocalBroadcast.Broadcast.traceOriginals (∑ i, c i • M i) =
      ∑ i, c i • NoLocalBroadcast.Broadcast.traceOriginals (M i) := by
  ext p q
  simp only [NoLocalBroadcast.Broadcast.traceOriginals, Matrix.of_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  symm
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm)

/-- (<=): a classical-classical state is locally broadcastable. -/
theorem cc_lb {a b : Type} [Fintype a] [DecidableEq a] [Nonempty a] [Fintype b] [DecidableEq b]
    [Nonempty b] (ρ : Matrix (a × b) (a × b) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ)
    (h : NoLocalBroadcast.Broadcast.IsClassicalClassical ρ) :
    NoLocalBroadcast.Broadcast.IsLocallyBroadcastable ρ := by
  obtain ⟨k, l, e, f, p, he, hf, hp0, hp1, hρe⟩ := h
  obtain ⟨K, hK, hKe⟩ := copier e he
  obtain ⟨L, hL, hLf⟩ := copier f hf
  have hσ : NoLocalBroadcast.Broadcast.localApply K L ρ =
      ∑ ij : Fin k × Fin l, (p ij : ℂ) •
        ((QAlgorithms.pureDensity (e ij.1) ⊗ₖ QAlgorithms.pureDensity (e ij.1)) ⊗ₖ
          (QAlgorithms.pureDensity (f ij.2) ⊗ₖ QAlgorithms.pureDensity (f ij.2))) := by
    rw [hρe, la_sum]
    simp only [la_kron, hKe, hLf]
  refine ⟨2, 2, K, L, hK, hL, ⟨by unfold NoLocalBroadcast.Broadcast.localApply; exact kraus_psd _ ρ hρ.1, ?_⟩, ?_, ?_⟩
  · rw [hσ, Matrix.trace_sum]
    simp only [Matrix.trace_smul, Matrix.trace_kronecker, pd_trace e he, pd_trace f hf, mul_one,
      smul_eq_mul]
    rw [← Complex.ofReal_sum, hp1, Complex.ofReal_one]
  · rw [hσ, tc_sum, hρe]
    simp only [tc_kron, pd_trace e he, pd_trace f hf, mul_one, one_smul]
  · rw [hσ, to_sum, hρe]
    simp only [to_kron, pd_trace e he, pd_trace f hf, mul_one, one_smul]

end P412

open NoLocalBroadcast.Broadcast in
theorem solution {a b : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) :
    IsLocallyBroadcastable ρ ↔ IsClassicalClassical ρ := by
  exact ⟨P412.C4 ρ hρ, P412.cc_lb ρ hρ⟩
