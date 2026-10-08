-- Prove2me | solution 1 for HighDimStat.Rkhs.rkhs_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T16:56:55.031056+00:00
-- url     : https://prove2.me/submissions/731a5807-da4e-4084-985a-90a9a7e1793f

import Mathlib

set_option maxHeartbeats 1000000

/-!
# Uniqueness of the RKHS of a PSD kernel (Moore-Aronszajn, uniqueness half)

Self-contained submission: the operator-matrix bridge to Mathlib's `RKHS.OfKernel`
complements, the finitely-supported kernel-section combinations, and the dense-isometry
extension argument. Assembles `RkhsUniqueness.exists_intertwined_equiv`.
-/

open Finset

open scoped RealInnerProductSpace

noncomputable section

namespace RkhsExistence

/-- Scalar multiplication operator `v ↦ c * v` on `ℝ`. -/
def toOp (c : ℝ) : ℝ →L[ℝ] ℝ := (ContinuousLinearMap.id ℝ ℝ).smulRight c

@[simp] lemma toOp_apply (c v : ℝ) : toOp c v = c * v := by
  simp [toOp, ContinuousLinearMap.smulRight_apply, mul_comm]

lemma star_toOp (c : ℝ) : star (toOp c) = toOp c := by
  apply ContinuousLinearMap.ext
  intro v
  refine ext_inner_right ℝ (fun x => ?_)
  rw [show (star (toOp c)) v = (toOp c).adjoint v from rfl,
    ContinuousLinearMap.adjoint_inner_left]
  simp [toOp_apply, Real.inner_apply, mul_assoc, mul_left_comm, mul_comm]

/-- The scalar kernel as an operator-valued matrix. -/
def opK {X : Type*} (K : X → X → ℝ) : Matrix X X (ℝ →L[ℝ] ℝ) :=
  Matrix.of fun x y => toOp (K x y)

lemma opK_hermitian {X : Type*} (K : X → X → ℝ) (hsym : ∀ x y, K x y = K y x) :
    (opK K).IsHermitian :=
  (by ext x y; simp [Matrix.conjTranspose_apply, opK, star_toOp, hsym x y] :
    (opK K).conjTranspose = opK K)

/-- Bridge: Finsupp-indexed quadratic forms are `Fin`-indexed ones. -/
lemma finsupp_to_fin {X : Type*} (G : X → X → ℝ) (f : X →₀ ℝ) :
    f.sum (fun x w => f.sum (fun x' w' => G x x' * w * w'))
      = ∑ i : Fin f.support.card, ∑ j : Fin f.support.card,
          G (f.support.equivFin.symm i) (f.support.equivFin.symm j)
            * f (f.support.equivFin.symm i) * f (f.support.equivFin.symm j) := by
  classical
  set S := f.support with hS
  set E : Fin S.card → X := fun i => S.equivFin.symm i with hE
  have hinj : ∀ i ∈ (Finset.univ : Finset (Fin S.card)), E i ∈ S :=
    fun i _ => S.equivFin.symm i |>.2
  have hreindex : ∀ (G : X → ℝ), (∑ i : Fin S.card, G (E i)) = ∑ x ∈ S, G x := by
    intro G
    refine Finset.sum_nbij E (fun i _ => hinj i (Finset.mem_univ i)) ?_ ?_ (fun x _ => rfl)
    · intro a _ b _ hab
      exact S.equivFin.symm.injective (by simpa [hE] using hab)
    · rintro x hx
      exact ⟨S.equivFin ⟨x, hx⟩, Finset.mem_univ _, by simp [hE]⟩
  rw [Finsupp.sum, ← hreindex (fun x => f.sum (fun x' w' => G x x' * f x * w'))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.sum, ← hreindex (fun x => G (E i) x * f (E i) * f x)]

lemma opK_posSemidef {X : Type*} (K : X → X → ℝ) (hsym : ∀ x y, K x y = K y x)
    (hpsd : ∀ (n : ℕ) (x : Fin n → X) (α : Fin n → ℝ),
      0 ≤ ∑ i, ∑ j, α i * α j * K (x i) (x j)) :
    (opK K).PosSemidef := by
  have htfae := RKHS.posSemidef_tfae (K := opK K)
  have hform : (opK K).IsHermitian ∧ ∀ (vv : X →₀ ℝ),
      0 ≤ RCLike.re (vv.sum fun x w => vv.sum fun x' w' => inner ℝ ((opK K x' x) w) w') := by
    refine ⟨opK_hermitian K hsym, ?_⟩
    intro vv
    have hconv : vv.sum (fun x w => vv.sum (fun x' w' => inner ℝ ((opK K x' x) w) w'))
        = vv.sum (fun x w => vv.sum (fun x' w' => K x' x * w * w')) := by
      refine Finsupp.sum_congr fun x _ => ?_
      refine Finsupp.sum_congr fun x' _ => ?_
      simp only [opK, Matrix.of_apply, toOp_apply, Real.inner_apply]
    rw [hconv]
    have hre : RCLike.re (vv.sum (fun x w => vv.sum (fun x' w' => K x' x * w * w')))
        = vv.sum (fun x w => vv.sum (fun x' w' => K x' x * w * w')) := by simp
    rw [hre, finsupp_to_fin (fun x x' => K x' x) vv]
    have hfin := hpsd vv.support.card
      (fun i => vv.support.equivFin.symm i) (fun i => vv (vv.support.equivFin.symm i))
    convert hfin using 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsym]
    ring
  exact (htfae.out 2 0).mp hform


end RkhsExistence

namespace RkhsUniqueness

/-- Two continuous maps into a Hausdorff space agreeing on a dense set are equal. -/
theorem eq_of_continuous_of_dense {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [T2Space β] {f g : α → β} (hf : Continuous f) (hg : Continuous g) {s : Set α}
    (hs : Dense s) (h : ∀ x ∈ s, f x = g x) : f = g := by
  have hcl : IsClosed {x | f x = g x} := isClosed_eq hf hg
  have hsub : s ⊆ {x | f x = g x} := fun x hx => h x hx
  funext x
  exact closure_minimal hsub hcl (hs x)

section

variable {X : Type} {K : X → X → ℝ}
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The canonical map from formal finite combinations of kernel sections into `H`. -/
def iota (feature : X → H) : ((X × ℝ) →₀ ℝ) →ₗ[ℝ] H :=
  Finsupp.lsum ℝ (fun xv : X × ℝ =>
    LinearMap.smulRight (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (xv.2 • feature xv.1))

lemma iota_apply (feature : X → H) (f : (X × ℝ) →₀ ℝ) :
    iota feature f = f.sum (fun (xv : X × ℝ) c => c • (xv.2 • feature xv.1)) := rfl

lemma iota_single (feature : X → H) (x : X) (v : ℝ) :
    iota feature (Finsupp.single (x, v) 1) = v • feature x := by
  rw [iota_apply, Finsupp.sum_single_index]
  · simp
  · simp

/-- Inner products of kernel sections reproduce the kernel. -/
lemma inner_feature' {toFun : H → X → ℝ} (feature : X → H)
    (hmem : ∀ x : X, toFun (feature x) = fun y => K y x)
    (hrepr : ∀ (u : H) (x : X), inner ℝ u (feature x) = toFun u x)
    (x y : X) : inner ℝ (feature x) (feature y) = K y x :=
  (hrepr (feature x) y).trans (congrFun (hmem x) y)

lemma inner_iota {toFun : H → X → ℝ} (feature : X → H)
    (hmem : ∀ x : X, toFun (feature x) = fun y => K y x)
    (hrepr : ∀ (u : H) (x : X), inner ℝ u (feature x) = toFun u x)
    (f g : (X × ℝ) →₀ ℝ) :
    inner ℝ (iota feature f) (iota feature g)
      = f.sum (fun (xv : X × ℝ) c => g.sum (fun (xv' : X × ℝ) d =>
          c * d * (xv.2 * xv'.2) * K xv'.1 xv.1)) := by
  rw [iota_apply, iota_apply, Finsupp.sum_inner]
  refine Finsupp.sum_congr fun (y, u) _ => ?_
  rw [Finsupp.inner_sum]
  refine Finsupp.sum_congr fun (x, v) _ => ?_
  rw [inner_smul_left, inner_smul_right, inner_smul_right, inner_smul_left,
    inner_feature' feature hmem hrepr y x]
  have h1 : (starRingEnd ℝ) (f (y, u)) = f (y, u) := by simp
  have h2 : (starRingEnd ℝ) u = u := by simp
  rw [h1, h2]
  ring

/-- A vector orthogonal to the range of `iota` vanishes. -/
lemma eq_zero_of_inner_iota {toFun : H → X → ℝ} (feature : X → H)
    (hrepr : ∀ (u : H) (x : X), inner ℝ u (feature x) = toFun u x)
    (hinj : Function.Injective toFun)
    (u : H) (h : ∀ f : (X × ℝ) →₀ ℝ, inner ℝ (iota feature f) u = 0) : u = 0 := by
  have hfeat : ∀ x : X, inner ℝ (feature x) u = 0 := by
    intro x
    have h0 := h (Finsupp.single (x, 1) 1)
    rw [iota_single, inner_smul_left] at h0
    simp at h0
    exact h0
  have hx : ∀ x : X, toFun u x = 0 := by
    intro x
    rw [← hrepr u x, real_inner_comm, hfeat x]
  have h0 : ∀ x : X, toFun 0 x = 0 := by
    intro x
    rw [← hrepr 0 x, inner_zero_left]
  refine hinj (funext fun x => ?_)
  rw [hx x, h0 x]

lemma denseRange_iota {toFun : H → X → ℝ} (feature : X → H)
    (hrepr : ∀ (u : H) (x : X), inner ℝ u (feature x) = toFun u x)
    (hinj : Function.Injective toFun) : DenseRange (iota feature) := by
  have hM : (LinearMap.range (iota feature))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u hu
    exact eq_zero_of_inner_iota feature hrepr hinj u
      (fun f => Submodule.inner_right_of_mem_orthogonal
        (LinearMap.mem_range_self (iota feature) f) hu)
  have h2 : (LinearMap.range (iota feature)).topologicalClosure = ⊤ := by
    refine Submodule.orthogonal_eq_bot_iff.mp ?_
    exact (Submodule.orthogonal_closure _).trans hM
  have hd : Dense ((LinearMap.range (iota feature) : Set H)) := by
    rw [dense_iff_closure_eq,
      ← (LinearMap.range (iota feature)).topologicalClosure_coe, h2]
    simp
  rwa [LinearMap.coe_range] at hd

end

section Both

variable {X : Type} {K : X → X → ℝ}
  {H₁ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  {H₂ : Type} [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
  (toFun₁ : H₁ → X → ℝ) (feature₁ : X → H₁)
  (hmem₁ : ∀ x : X, toFun₁ (feature₁ x) = fun y => K y x)
  (hrepr₁ : ∀ (u : H₁) (x : X), inner ℝ u (feature₁ x) = toFun₁ u x)
  (hinj₁ : Function.Injective toFun₁)
  (toFun₂ : H₂ → X → ℝ) (feature₂ : X → H₂)
  (hmem₂ : ∀ x : X, toFun₂ (feature₂ x) = fun y => K y x)
  (hrepr₂ : ∀ (u : H₂) (x : X), inner ℝ u (feature₂ x) = toFun₂ u x)
  (hinj₂ : Function.Injective toFun₂)

/-- Inner products of transported combinations agree between the two spaces. -/
lemma inner_iota_iota (feature₁ : X → H₁) (hmem₁ : ∀ x : X, toFun₁ (feature₁ x) = fun y => K y x)
    (hrepr₁ : ∀ (u : H₁) (x : X), inner ℝ u (feature₁ x) = toFun₁ u x)
    (feature₂ : X → H₂) (hmem₂ : ∀ x : X, toFun₂ (feature₂ x) = fun y => K y x)
    (hrepr₂ : ∀ (u : H₂) (x : X), inner ℝ u (feature₂ x) = toFun₂ u x)
    (f g : (X × ℝ) →₀ ℝ) :
    inner ℝ (iota feature₁ f) (iota feature₁ g)
      = inner ℝ (iota feature₂ f) (iota feature₂ g) := by
  rw [inner_iota feature₁ hmem₁ hrepr₁ f g,
    inner_iota feature₂ hmem₂ hrepr₂ f g]

end Both

section CompletionBridge

open RkhsExistence in
/-- The H₀ inner product of the kernel-section space, in canonical form. -/
lemma h0_inner_canonical {X : Type} (K : X → X → ℝ)
    (hsym : ∀ x y : X, K x y = K y x)
    (hpsd : ∀ (n : ℕ) (x : Fin n → X) (c : Fin n → ℝ),
      0 ≤ ∑ i, ∑ j, c i * c j * K (x i) (x j))
    [Fact ((opK K).PosSemidef)] (f g : RKHS.H₀ (opK K)) :
    inner ℝ f g
      = f.sum (fun (xv : X × ℝ) c => g.sum (fun (xv' : X × ℝ) d =>
          c * d * (xv.2 * xv'.2) * K xv'.1 xv.1)) := by
  have h1 : inner ℝ f g
      = (RKHS.instPreInnerProductSpaceCoreH₀ (K := opK K)).inner f g := rfl
  have h2 : (RKHS.instPreInnerProductSpaceCoreH₀ (K := opK K)).inner f g
      = f.sum (fun (y, u) z => g.sum (fun (x, v) w =>
          (star z) * w * inner ℝ ((opK K x y) u) v)) := rfl
  rw [h1, h2]
  refine Finsupp.sum_congr fun (y, u) _ => Finsupp.sum_congr fun (x, v) _ => ?_
  simp only [opK, Matrix.of_apply, toOp_apply, Real.inner_apply, star_trivial]
  ring

end CompletionBridge

section Extension

variable {X : Type} {K : X → X → ℝ}
  {H₁ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  {H₂ : Type} [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]

lemma kernel_symm' (feature : X → H₁) {toFun : H₁ → X → ℝ}
    (hmem : ∀ x : X, toFun (feature x) = fun y => K y x)
    (hrepr : ∀ (u : H₁) (x : X), inner ℝ u (feature x) = toFun u x)
    (x y : X) : K x y = K y x := by
  have h1 : inner ℝ (feature x) (feature y) = K y x :=
    (hrepr (feature x) y).trans (congrFun (hmem x) y)
  have h2 : inner ℝ (feature y) (feature x) = K x y :=
    (hrepr (feature y) x).trans (congrFun (hmem y) x)
  rw [← h1, ← h2, real_inner_comm]

lemma kernel_psd (feature : X → H₁) {toFun : H₁ → X → ℝ}
    (hmem : ∀ x : X, toFun (feature x) = fun y => K y x)
    (hrepr : ∀ (u : H₁) (x : X), inner ℝ u (feature x) = toFun u x)
    (n : ℕ) (x : Fin n → X) (α : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, α i * α j * K (x i) (x j) := by
  have hrow : ∀ i : Fin n, inner ℝ (α i • feature (x i)) (∑ j, α j • feature (x j))
      = ∑ j, α i * α j * K (x i) (x j) := by
    intro i
    rw [real_inner_comm, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, inner_smul_right,
      inner_feature' feature hmem hrepr (x j) (x i)]
    have h2 : (starRingEnd ℝ) (α j) = α j := by simp
    rw [h2]
    ring
  have hexp : ∑ i, ∑ j, α i * α j * K (x i) (x j)
      = inner ℝ (∑ i, α i • feature (x i)) (∑ j, α j • feature (x j)) := by
    rw [sum_inner]
    exact Finset.sum_congr rfl fun i _ => (hrow i).symm
  rw [hexp]
  exact real_inner_self_nonneg

end Extension

section Main

variable {X : Type} {K : X → X → ℝ}
  {H₁ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  {H₂ : Type} [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]

/-- Any two reproducing-kernel presentations of the same kernel are connected by a
linear equivalence intertwining the function embeddings. -/
theorem exists_intertwined_equiv
    (toFun₁ : H₁ → X → ℝ) (feature₁ : X → H₁)
    (hmem₁ : ∀ x : X, toFun₁ (feature₁ x) = fun y => K y x)
    (hrepr₁ : ∀ (u : H₁) (x : X), inner ℝ u (feature₁ x) = toFun₁ u x)
    (hinj₁ : Function.Injective toFun₁)
    (toFun₂ : H₂ → X → ℝ) (feature₂ : X → H₂)
    (hmem₂ : ∀ x : X, toFun₂ (feature₂ x) = fun y => K y x)
    (hrepr₂ : ∀ (u : H₂) (x : X), inner ℝ u (feature₂ x) = toFun₂ u x)
    (hinj₂ : Function.Injective toFun₂) :
    ∃ e : H₁ ≃ₗ[ℝ] H₂, ∀ u : H₁, toFun₂ (e u) = toFun₁ u := by
  classical
  -- the kernel is PSD and symmetric, derived from the first presentation
  have hsym : ∀ x y, K x y = K y x := kernel_symm' feature₁ hmem₁ hrepr₁
  have hpsd : ∀ (n : ℕ) (x : Fin n → X) (α : Fin n → ℝ),
      0 ≤ ∑ i, ∑ j, α i * α j * K (x i) (x j) := kernel_psd feature₁ hmem₁ hrepr₁
  haveI hFact : Fact ((RkhsExistence.opK K).PosSemidef) :=
    Fact.mk (RkhsExistence.opK_posSemidef K hsym hpsd)
  -- they transport the H₀ inner product identically
  have hinner₁ : ∀ f g : RKHS.H₀ (RkhsExistence.opK K),
      inner ℝ (iota feature₁ f) (iota feature₁ g) = inner ℝ f g := by
    intro f g
    rw [h0_inner_canonical K hsym hpsd f g,
      inner_iota feature₁ hmem₁ hrepr₁ f g]
  have hinner₂ : ∀ f g : RKHS.H₀ (RkhsExistence.opK K),
      inner ℝ (iota feature₂ f) (iota feature₂ g) = inner ℝ f g := by
    intro f g
    rw [h0_inner_canonical K hsym hpsd f g,
      inner_iota feature₂ hmem₂ hrepr₂ f g]
  -- the maps are isometries, hence uniformly continuous
  have hiso₁ : Isometry (iota feature₁ : RKHS.H₀ (RkhsExistence.opK K) → H₁) :=
    (LinearMap.isometryOfInner (iota feature₁)
      (fun f g => hinner₁ f g)).isometry
  have hiso₂ : Isometry (iota feature₂ : RKHS.H₀ (RkhsExistence.opK K) → H₂) :=
    (LinearMap.isometryOfInner (iota feature₂)
      (fun f g => hinner₂ f g)).isometry
  -- the two extension maps out of the canonical completion
  set B := UniformSpace.Completion.extension
    (iota feature₁ : RKHS.H₀ (RkhsExistence.opK K) → H₁) with hBdef
  set A := UniformSpace.Completion.extension
    (iota feature₂ : RKHS.H₀ (RkhsExistence.opK K) → H₂) with hAdef
  have hBcont : Continuous B := UniformSpace.Completion.continuous_extension
  have hAcont : Continuous A := UniformSpace.Completion.continuous_extension
  have hBcoe : ∀ f : RKHS.H₀ (RkhsExistence.opK K),
      B ((f : RKHS.OfKernel (RkhsExistence.opK K))) = iota feature₁ f :=
    UniformSpace.Completion.extension_coe hiso₁.uniformContinuous
  have hAcoe : ∀ f : RKHS.H₀ (RkhsExistence.opK K),
      A ((f : RKHS.OfKernel (RkhsExistence.opK K))) = iota feature₂ f :=
    UniformSpace.Completion.extension_coe hiso₂.uniformContinuous
  -- density of the canonical image in the completion
  have hdense : Dense (Set.range
      (fun f : RKHS.H₀ (RkhsExistence.opK K) =>
        (f : RKHS.OfKernel (RkhsExistence.opK K)))) :=
    UniformSpace.Completion.denseRange_coe
  -- B preserves all inner products, by continuity from the dense image
  have hBinner : ∀ x y : RKHS.OfKernel (RkhsExistence.opK K),
      inner ℝ (B x) (B y) = inner ℝ x y := by
    have h := eq_of_continuous_of_dense
      (f := fun p : RKHS.OfKernel (RkhsExistence.opK K)
          × RKHS.OfKernel (RkhsExistence.opK K) => inner ℝ (B p.1) (B p.2))
      (g := fun p : RKHS.OfKernel (RkhsExistence.opK K)
          × RKHS.OfKernel (RkhsExistence.opK K) => inner ℝ p.1 p.2)
      (hf := by continuity) (hg := by continuity)
      (hs := hdense.prod hdense)
      (h := by
        rintro ⟨p1, p2⟩ hp
        obtain ⟨f, rfl⟩ := hp.1
        obtain ⟨g, rfl⟩ := hp.2
        rw [hBcoe f, hBcoe g, UniformSpace.Completion.inner_coe, hinner₁ f g])
    intro x y
    exact congrFun h (x, y)
  -- B is an isometry
  have hBiso : Isometry B := by
    refine Isometry.of_dist_eq fun x y => ?_
    have h1 : inner ℝ (B x - B y) (B x - B y) = inner ℝ (x - y) (x - y) := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_sub_left,
        hBinner, hBinner, hBinner, hBinner, inner_sub_right, inner_sub_right]
    have h2 : ‖B x - B y‖ ^ 2 = ‖x - y‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, h1]
    calc dist (B x) (B y) = ‖B x - B y‖ := dist_eq_norm (B x) (B y)
      _ = ‖x - y‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2
      _ = dist x y := (dist_eq_norm x y).symm
  have hBinj : Function.Injective B := hBiso.injective
  -- B is surjective: its range is complete, hence closed, and contains a dense set
  have hBsurj : Function.Surjective B := by
    have hcomp : IsComplete (Set.range B) :=
      (completeSpace_iff_isComplete_range hBiso.isUniformInducing).mp inferInstance
    have hcl : IsClosed (Set.range B) := hcomp.isClosed
    have hdense' : Dense (Set.range (iota feature₁)) :=
      denseRange_iota feature₁ hrepr₁ hinj₁
    have hrsub : Set.range (iota feature₁) ⊆ Set.range B := by
      rintro _ ⟨f, rfl⟩
      exact ⟨(f : RKHS.OfKernel (RkhsExistence.opK K)), by rw [hBcoe f]⟩
    have : Set.univ ⊆ Set.range B := by
      rw [← hdense'.closure_eq]
      exact closure_minimal hrsub hcl
    exact Set.range_eq_univ.mp (Set.eq_univ_of_univ_subset this)
  -- A preserves all inner products, by continuity from the dense image
  have hAinner : ∀ x y : RKHS.OfKernel (RkhsExistence.opK K),
      inner ℝ (A x) (A y) = inner ℝ x y := by
    have h := eq_of_continuous_of_dense
      (f := fun p : RKHS.OfKernel (RkhsExistence.opK K)
          × RKHS.OfKernel (RkhsExistence.opK K) => inner ℝ (A p.1) (A p.2))
      (g := fun p : RKHS.OfKernel (RkhsExistence.opK K)
          × RKHS.OfKernel (RkhsExistence.opK K) => inner ℝ p.1 p.2)
      (hf := by continuity) (hg := by continuity)
      (hs := hdense.prod hdense)
      (h := by
        rintro ⟨p1, p2⟩ hp
        obtain ⟨f, rfl⟩ := hp.1
        obtain ⟨g, rfl⟩ := hp.2
        rw [hAcoe f, hAcoe g, UniformSpace.Completion.inner_coe, hinner₂ f g])
    intro x y
    exact congrFun h (x, y)
  -- likewise A is a bijection
  have hAiso : Isometry A := by
    refine Isometry.of_dist_eq fun x y => ?_
    have h1 : inner ℝ (A x - A y) (A x - A y) = inner ℝ (x - y) (x - y) := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_sub_left,
        hAinner, hAinner, hAinner, hAinner, inner_sub_right, inner_sub_right]
    have h2 : ‖A x - A y‖ ^ 2 = ‖x - y‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, h1]
    calc dist (A x) (A y) = ‖A x - A y‖ := dist_eq_norm (A x) (A y)
      _ = ‖x - y‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2
      _ = dist x y := (dist_eq_norm x y).symm
  have hAinj : Function.Injective A := hAiso.injective
  have hAsurj : Function.Surjective A := by
    have hcomp : IsComplete (Set.range A) :=
      (completeSpace_iff_isComplete_range hAiso.isUniformInducing).mp inferInstance
    have hcl : IsClosed (Set.range A) := hcomp.isClosed
    have hdense'' : Dense (Set.range (iota feature₂)) :=
      denseRange_iota feature₂ hrepr₂ hinj₂
    have hrsub : Set.range (iota feature₂) ⊆ Set.range A := by
      rintro _ ⟨f, rfl⟩
      exact ⟨(f : RKHS.OfKernel (RkhsExistence.opK K)), by rw [hAcoe f]⟩
    have : Set.univ ⊆ Set.range A := by
      rw [← hdense''.closure_eq]
      exact closure_minimal hrsub hcl
    exact Set.range_eq_univ.mp (Set.eq_univ_of_univ_subset this)
  -- the transported equivalence
  -- B is linear: additivity and scalar-multiplicativity by density
  have hBadd : ∀ (x y : RKHS.OfKernel (RkhsExistence.opK K)), B (x + y) = B x + B y := by
    intro x y
    have hstep : ∀ (v : RKHS.OfKernel (RkhsExistence.opK K))
        (g : RKHS.H₀ (RkhsExistence.opK K)),
        B (v + (g : _)) = B v + B (g : _) := by
      intro v g
      have h := eq_of_continuous_of_dense
        (f := fun w : RKHS.OfKernel (RkhsExistence.opK K) => B (w + (g : _)))
        (g := fun w : RKHS.OfKernel (RkhsExistence.opK K) => B w + B (g : _))
        (hf := by continuity) (hg := by continuity)
        (hs := hdense)
        (h := by
          intro w hw
          obtain ⟨f, rfl⟩ := hw
          change B ((f : RKHS.OfKernel (RkhsExistence.opK K))
              + (g : RKHS.OfKernel (RkhsExistence.opK K)))
            = B (f : RKHS.OfKernel (RkhsExistence.opK K))
              + B (g : RKHS.OfKernel (RkhsExistence.opK K))
          rw [← UniformSpace.Completion.coe_add f g, hBcoe (f + g), hBcoe f, hBcoe g,
            map_add])
      exact congrFun h v
    have h := eq_of_continuous_of_dense
      (f := fun v : RKHS.OfKernel (RkhsExistence.opK K) => B (x + v))
      (g := fun v : RKHS.OfKernel (RkhsExistence.opK K) => B x + B v)
      (hf := by continuity) (hg := by continuity)
      (hs := hdense)
      (h := by
        intro v hv
        obtain ⟨g, rfl⟩ := hv
        exact hstep x g)
    exact congrFun h y
  have hBsmul : ∀ (c : ℝ) (x : RKHS.OfKernel (RkhsExistence.opK K)),
      B (c • x) = c • B x := by
    intro c x
    have h := eq_of_continuous_of_dense
      (f := fun w : RKHS.OfKernel (RkhsExistence.opK K) => B (c • w))
      (g := fun w : RKHS.OfKernel (RkhsExistence.opK K) => c • B w)
      (hf := hBcont.comp (continuous_const_smul c)) (hg := hBcont.const_smul c)
      (hs := hdense)
      (h := by
        intro w hw
        obtain ⟨f, rfl⟩ := hw
        change B (c • (f : RKHS.OfKernel (RkhsExistence.opK K)))
          = c • B (f : RKHS.OfKernel (RkhsExistence.opK K))
        rw [← UniformSpace.Completion.coe_smul c f, hBcoe (c • f), hBcoe f, map_smul])
    exact congrFun h x
  have hAadd : ∀ (x y : RKHS.OfKernel (RkhsExistence.opK K)), A (x + y) = A x + A y := by
    intro x y
    have hstep : ∀ (v : RKHS.OfKernel (RkhsExistence.opK K))
        (g : RKHS.H₀ (RkhsExistence.opK K)),
        A (v + (g : _)) = A v + A (g : _) := by
      intro v g
      have h := eq_of_continuous_of_dense
        (f := fun w : RKHS.OfKernel (RkhsExistence.opK K) => A (w + (g : _)))
        (g := fun w : RKHS.OfKernel (RkhsExistence.opK K) => A w + A (g : _))
        (hf := by continuity) (hg := by continuity)
        (hs := hdense)
        (h := by
          intro w hw
          obtain ⟨f, rfl⟩ := hw
          change A ((f : RKHS.OfKernel (RkhsExistence.opK K))
              + (g : RKHS.OfKernel (RkhsExistence.opK K)))
            = A (f : RKHS.OfKernel (RkhsExistence.opK K))
              + A (g : RKHS.OfKernel (RkhsExistence.opK K))
          rw [← UniformSpace.Completion.coe_add f g, hAcoe (f + g), hAcoe f, hAcoe g,
            map_add])
      exact congrFun h v
    have h := eq_of_continuous_of_dense
      (f := fun v : RKHS.OfKernel (RkhsExistence.opK K) => A (x + v))
      (g := fun v : RKHS.OfKernel (RkhsExistence.opK K) => A x + A v)
      (hf := by continuity) (hg := by continuity)
      (hs := hdense)
      (h := by
        intro v hv
        obtain ⟨g, rfl⟩ := hv
        exact hstep x g)
    exact congrFun h y
  have hAsmul : ∀ (c : ℝ) (x : RKHS.OfKernel (RkhsExistence.opK K)),
      A (c • x) = c • A x := by
    intro c x
    have h := eq_of_continuous_of_dense
      (f := fun w : RKHS.OfKernel (RkhsExistence.opK K) => A (c • w))
      (g := fun w : RKHS.OfKernel (RkhsExistence.opK K) => c • A w)
      (hf := hAcont.comp (continuous_const_smul c)) (hg := hAcont.const_smul c)
      (hs := hdense)
      (h := by
        intro w hw
        obtain ⟨f, rfl⟩ := hw
        change A (c • (f : RKHS.OfKernel (RkhsExistence.opK K)))
          = c • A (f : RKHS.OfKernel (RkhsExistence.opK K))
        rw [← UniformSpace.Completion.coe_smul c f, hAcoe (c • f), hAcoe f, map_smul])
    exact congrFun h x
  have hBbeth : Function.Bijective B := ⟨hBinj, hBsurj⟩
  set Bb := (Equiv.ofBijective B hBbeth) with hBb
  have hsymmapp : ∀ x : RKHS.OfKernel (RkhsExistence.opK K), Bb.symm (B x) = x :=
    fun x => Equiv.symm_apply_apply (Equiv.ofBijective B hBbeth) x
  have hsymmimg : ∀ u : H₁, B (Bb.symm u) = u :=
    fun u => Equiv.apply_symm_apply (Equiv.ofBijective B hBbeth) u
  have hsymmadd : ∀ u v : H₁, Bb.symm (u + v) = Bb.symm u + Bb.symm v := by
    intro u v
    refine hBinj ?_
    rw [hsymmimg (u + v), hBadd, hsymmimg u, hsymmimg v]
  -- Bb.symm is an isometry, hence continuous
  have hsymmiso : Isometry (fun u : H₁ => Bb.symm u) := by
    refine Isometry.of_dist_eq fun u v => ?_
    have h1 : dist (B (Bb.symm u)) (B (Bb.symm v))
        = dist (Bb.symm u) (Bb.symm v) := hBiso.dist_eq _ _
    rw [hsymmimg u, hsymmimg v] at h1
    exact h1.symm
  have hsymmcont : Continuous (fun u : H₁ => Bb.symm u) := hsymmiso.continuous
  -- the candidate equivalence
  set e₀ : H₁ → H₂ := fun u => A (Bb.symm u) with he₀
  have hecont : Continuous e₀ := hAcont.comp hsymmcont
  have headd : ∀ u v : H₁, e₀ (u + v) = e₀ u + e₀ v := by
    intro u v
    show A (Bb.symm (u + v)) = A (Bb.symm u) + A (Bb.symm v)
    rw [hsymmadd u v, hAadd]
  have hesmul : ∀ (c : ℝ) (u : H₁), e₀ (c • u) = c • e₀ u := by
    intro c u
    have hsymmsmul : Bb.symm (c • u) = c • Bb.symm u := by
      refine hBinj ?_
      rw [hsymmimg (c • u), hBsmul, hsymmimg u]
    show A (Bb.symm (c • u)) = c • A (Bb.symm u)
    rw [hsymmsmul, hAsmul]
  have heinj : Function.Injective e₀ := by
    intro u v huv
    have h1 : A (Bb.symm u) = A (Bb.symm v) := huv
    have h2 : Bb.symm u = Bb.symm v := hAinj h1
    exact Bb.symm.injective h2
  have hesurj : Function.Surjective e₀ := by
    intro v
    obtain ⟨x, hx⟩ := hAsurj v
    refine ⟨Bb x, ?_⟩
    show A (Bb.symm (Bb x)) = v
    rw [Equiv.symm_apply_apply]
    exact hx
  -- intertwining: pointwise in `x`, continuity + agreement on the dense range
  have hint : ∀ (u : H₁) (x : X), toFun₂ (e₀ u) x = toFun₁ u x := by
    intro u x
    have h := eq_of_continuous_of_dense
      (f := fun w : H₁ => toFun₂ (e₀ w) x)
      (g := fun w : H₁ => toFun₁ w x)
      (hf := by
        have : Continuous fun w : H₁ => toFun₂ (e₀ w) x := by
          have h1 : ∀ w : H₁, toFun₂ (e₀ w) x
              = inner ℝ (e₀ w) (feature₂ x) := fun w => (hrepr₂ (e₀ w) x).symm
          rw [funext h1]
          exact (hecont).inner continuous_const
        exact this)
      (hg := by
        have : Continuous fun w : H₁ => toFun₁ w x := by
          have h1 : ∀ w : H₁, toFun₁ w x = inner ℝ w (feature₁ x) :=
            fun w => (hrepr₁ w x).symm
          rw [funext h1]
          exact continuous_id.inner continuous_const
        exact this)
      (hs := (denseRange_iota feature₁ hrepr₁ hinj₁))
      (h := by
        intro w hw
        obtain ⟨f, rfl⟩ := hw
        have hbfs : Bb.symm (iota feature₁ f)
            = (f : RKHS.OfKernel (RkhsExistence.opK K)) := by
          have h1 : B ((f : RKHS.OfKernel (RkhsExistence.opK K)))
              = iota feature₁ f := hBcoe f
          have h2 : Bb.symm (iota feature₁ f)
              = Bb.symm (B ((f : RKHS.OfKernel (RkhsExistence.opK K)))) := by
            rw [h1]
          rw [h2, hsymmapp]
        show toFun₂ (A (Bb.symm ((iota feature₁) f))) x = toFun₁ ((iota feature₁) f) x
        rw [hbfs, hAcoe f]
        rw [← hrepr₂ (iota feature₂ f) x, ← hrepr₁ (iota feature₁ f) x]
        have hg2 : (iota feature₂) (Finsupp.single (x, (1 : ℝ)) (1 : ℝ)) = feature₂ x := by
          rw [iota_single, one_smul]
        have hg1 : (iota feature₁) (Finsupp.single (x, (1 : ℝ)) (1 : ℝ)) = feature₁ x := by
          rw [iota_single, one_smul]
        have hii := inner_iota_iota toFun₁ toFun₂ feature₁ hmem₁ hrepr₁
          feature₂ hmem₂ hrepr₂ f (Finsupp.single (x, (1 : ℝ)) (1 : ℝ))
        rw [hg1, hg2] at hii
        exact hii.symm)
    exact congrFun h u
  have hlinmap : H₁ →ₗ[ℝ] H₂ :=
    { toFun := e₀
      map_add' := headd
      map_smul' := hesmul }
  refine ⟨LinearEquiv.ofBijective
    ({ toFun := e₀
       map_add' := headd
       map_smul' := hesmul } : H₁ →ₗ[ℝ] H₂)
    ⟨heinj, hesurj⟩, ?_⟩
  intro u
  exact funext (hint u)

end Main

end RkhsUniqueness


/-- The target statement: any two reproducing-kernel presentations of the same kernel
are connected by a linear equivalence intertwining the function embeddings. -/
theorem solution {X : Type} (K : X → X → ℝ)
    (H₁ H₂ : Type)
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
    (toFun₁ : H₁ → X → ℝ) (toFun₂ : H₂ → X → ℝ)
    (hlin₁ : ∀ (u v : H₁) (a b : ℝ),
      toFun₁ (a • u + b • v) = fun x => a * toFun₁ u x + b * toFun₁ v x)
    (hinj₁ : Function.Injective toFun₁) (feature₁ : X → H₁)
    (hmem₁ : ∀ x : X, toFun₁ (feature₁ x) = fun y => K y x)
    (hrepr₁ : ∀ (u : H₁) (x : X), inner ℝ u (feature₁ x) = toFun₁ u x)
    (hlin₂ : ∀ (u v : H₂) (a b : ℝ),
      toFun₂ (a • u + b • v) = fun x => a * toFun₂ u x + b * toFun₂ v x)
    (hinj₂ : Function.Injective toFun₂) (feature₂ : X → H₂)
    (hmem₂ : ∀ x : X, toFun₂ (feature₂ x) = fun y => K y x)
    (hrepr₂ : ∀ (u : H₂) (x : X), inner ℝ u (feature₂ x) = toFun₂ u x) :
    ∃ e : H₁ ≃ₗ[ℝ] H₂, ∀ u : H₁, toFun₂ (e u) = toFun₁ u :=
  RkhsUniqueness.exists_intertwined_equiv toFun₁ feature₁ hmem₁ hrepr₁ hinj₁
    toFun₂ feature₂ hmem₂ hrepr₂ hinj₂

