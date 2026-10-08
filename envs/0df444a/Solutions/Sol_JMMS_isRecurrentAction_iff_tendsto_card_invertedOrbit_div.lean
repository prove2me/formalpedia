-- Prove2me | solution 1 for JMMS.isRecurrentAction_iff_tendsto_card_invertedOrbit_div
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T12:46:24.857971+00:00
-- url     : https://prove2.me/submissions/5feb54ee-cd8c-4b1a-9820-43b0740785f9

import Mathlib
import Definitions.Def_IntervalExchange

section

/-! # Comparison of recurrence for symmetric random walks on a transitive `G`-set

`JMMS.IETRC.isRecurrentChain_comparison`: for a transitive action `G ↷ X`, a symmetric finitely
supported probability `μ` with generating support, and `x₀` with the `μ`-chain recurrent at `x₀`,
every symmetric finitely supported probability `ν` gives a chain recurrent at every `y`.

Route (analytic, no path space), with `P f (z) = ∑_g μ(g) f(g⁻¹ z)` and finitely supported
functions on `X`:

* **Renewal.** `p_{n+1} = a_{n+1} + ∑_{k ≤ n} f_k p_{n-k}`, where `p_n` is the law at time `n`,
  `a_n` the law of the walk killed at its first return, and `f_k` the first-return probabilities
  (`firstReturnProb`, identified with the kernel-free recursion). Hence, with
  `G_N = ∑_{n<N} p_n(o)`: transience (`∑ f_k < 1`) bounds `G_N`, and recurrence (`∑ f_k = 1`)
  makes `G_N` unbounded.
* **Dirichlet form.** `B(f,h) = ∑_g μ(g) ∑_z (f z - f(gz))(h z - h(gz)) = 2⟨f, h - P h⟩`
  (`μ` symmetric), `P` self-adjoint, so `⟨p_a, p_b⟩ = p_{a+b}(o)`.
* **Hardy inequality from a bounded Green function.** For `u = u_N = ∑_{n<N} p_n`,
  `u - P u = δ_o - p_N`, `B(u,u) ≤ 2 u(o)`, and `f(o) - ⟨f, p_N⟩ = B(f,u)/2`; with
  `⟨p_N, p_N⟩ = p_{2N}(o) → 0` this gives `f(o)² ≤ C · B(f,f)`.
* **Comparison.** Each step of `ν` is a word in `supp μ`, so `B_ν ≤ K · B_μ`; moving the base
  point costs one more such word.
* **Green function bound from Hardy** (as in Kaimanovich): `u(o)² ≤ C B_μ(u,u) ≤ 2C u(o)`.
-/

open IntervalExchange

set_option linter.unusedSectionVars false

namespace JMMS.IETRC

open Classical

variable {G X : Type*} [Group G] [MulAction G X]

/-! ## Finitely supported functions on `X` -/

/-- `f` has finite support. -/
def FS (f : X → ℝ) : Prop := (Function.support f).Finite

lemma FS.summable {f : X → ℝ} (hf : FS f) : Summable f :=
  summable_of_ne_finset_zero (s := Set.Finite.toFinset (s := Function.support f) hf)
    (fun b hb => by
      by_contra hne
      exact hb ((Set.Finite.mem_toFinset _).mpr hne))

lemma FS.of_zero {f f' g : X → ℝ} (hf : FS f) (hf' : FS f')
    (h : ∀ z, f z = 0 → f' z = 0 → g z = 0) : FS g := by
  refine (hf.union hf').subset ?_
  intro z hz
  by_contra hc
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc
  exact hz (h z hc.1 hc.2)

lemma FS.comp_smul {f : X → ℝ} (hf : FS f) (g : G) : FS (fun z => f (g • z)) := by
  have : (Function.support fun z => f (g • z)) = (fun z => g • z) ⁻¹' Function.support f := rfl
  rw [FS, this]
  exact hf.preimage (MulAction.injective g).injOn

lemma FS.mul_left {f : X → ℝ} (hf : FS f) (g : X → ℝ) : FS (fun z => g z * f z) :=
  hf.of_zero hf (fun z h _ => by simp [h])

lemma FS.mul_right {f : X → ℝ} (hf : FS f) (g : X → ℝ) : FS (fun z => f z * g z) :=
  hf.of_zero hf (fun z h _ => by simp [h])

lemma FS.add {f h : X → ℝ} (hf : FS f) (hh : FS h) : FS (fun z => f z + h z) :=
  hf.of_zero hh (fun z h1 h2 => by simp [h1, h2])

lemma FS.sub {f h : X → ℝ} (hf : FS f) (hh : FS h) : FS (fun z => f z - h z) :=
  hf.of_zero hh (fun z h1 h2 => by simp [h1, h2])

lemma FS.neg {f : X → ℝ} (hf : FS f) : FS (fun z => - f z) :=
  hf.of_zero hf (fun z h1 _ => by simp [h1])

lemma FS.delta (o : X) : FS (fun z : X => if z = o then (1 : ℝ) else 0) := by
  refine (Set.finite_singleton o).subset ?_
  intro z hz
  by_contra hc
  exact hz (by simp only [Set.mem_singleton_iff] at hc; simp [hc])

lemma FS.finset_sum {ι : Type*} (s : Finset ι) {F : ι → X → ℝ} (hF : ∀ i, FS (F i)) :
    FS (fun z => ∑ i ∈ s, F i z) := by
  induction s using Finset.induction_on with
  | empty => simp [FS]
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (hF i).add ih

lemma tsum_smul_comp (φ : X → ℝ) (g : G) : ∑' z, φ (g • z) = ∑' z, φ z :=
  (MulAction.toPerm g : Equiv.Perm X).tsum_eq φ

lemma hasSum_smul_comp {φ : X → ℝ} {c : ℝ} (g : G) (h : HasSum φ c) :
    HasSum (fun z => φ (g • z)) c :=
  ((MulAction.toPerm g : Equiv.Perm X).hasSum_iff (f := φ)).2 h

/-! ## The operator `P` -/

/-- `P f (z) = ∑_g μ(g) f(g⁻¹ z)`: one step of the law of the chain. -/
noncomputable def Pop (μ : G →₀ ℝ) (f : X → ℝ) (z : X) : ℝ :=
  ∑ g ∈ μ.support, μ g * f (g⁻¹ • z)

lemma Pop_FS (μ : G →₀ ℝ) {f : X → ℝ} (hf : FS f) : FS (Pop μ f) := by
  have hfin : (⋃ g ∈ (μ.support : Set G), (fun z => g • z) '' Function.support f).Finite :=
    Set.Finite.biUnion μ.support.finite_toSet fun g _ => hf.image _
  refine hfin.subset ?_
  intro z hz
  rw [Function.mem_support] at hz
  obtain ⟨g, hg, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  simp only [Set.mem_iUnion, Set.mem_image, Function.mem_support]
  exact ⟨g, hg, g⁻¹ • z, right_ne_zero_of_mul hne, smul_inv_smul g z⟩

lemma Pop_nonneg {μ : G →₀ ℝ} (hμ0 : ∀ g, 0 ≤ μ g) {f : X → ℝ} (hf : ∀ z, 0 ≤ f z) (z : X) :
    0 ≤ Pop μ f z :=
  Finset.sum_nonneg fun g _ => mul_nonneg (hμ0 g) (hf _)

lemma Pop_sum (μ : G →₀ ℝ) {ι : Type*} (s : Finset ι) (F : ι → X → ℝ) (z : X) :
    Pop μ (fun w => ∑ i ∈ s, F i w) z = ∑ i ∈ s, Pop μ (F i) z := by
  unfold Pop
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

lemma inv_mem_support {μ : G →₀ ℝ} (hs : IsSymmetric μ) {g : G} (hg : g ∈ μ.support) :
    g⁻¹ ∈ μ.support := by
  rw [Finsupp.mem_support_iff] at *
  rw [hs]; exact hg

lemma sum_inv {μ : G →₀ ℝ} (hs : IsSymmetric μ) (φ : G → ℝ) :
    ∑ g ∈ μ.support, μ g * φ g⁻¹ = ∑ g ∈ μ.support, μ g * φ g := by
  refine Finset.sum_nbij' (·⁻¹) (·⁻¹) (fun g hg => inv_mem_support hs hg)
    (fun g hg => inv_mem_support hs hg) (fun g _ => inv_inv g) (fun g _ => inv_inv g) ?_
  intro g _
  rw [hs]

lemma mass_one {μ : G →₀ ℝ} (hμ : ThompsonAmenability.IsProbability μ) :
    ∑ g ∈ μ.support, μ g = 1 := hμ.2

/-- Interchange of `∑'` over `X` and a finite sum. -/
lemma tsum_sum_mul (s : Finset G) (c : G → ℝ) (F : G → X → ℝ) (hF : ∀ g ∈ s, Summable (F g)) :
    ∑' z, ∑ g ∈ s, c g * F g z = ∑ g ∈ s, c g * ∑' z, F g z := by
  rw [Summable.tsum_finsetSum (fun g hg => (hF g hg).mul_left (c g))]
  simp_rw [tsum_mul_left]

lemma tsum_Pop {μ : G →₀ ℝ} (hμ : ThompsonAmenability.IsProbability μ) {f : X → ℝ} (hf : FS f) :
    ∑' z, Pop μ f z = ∑' z, f z := by
  unfold Pop
  rw [tsum_sum_mul _ _ _ (fun g _ => (hf.comp_smul g⁻¹).summable)]
  simp_rw [tsum_smul_comp f]
  rw [← Finset.sum_mul, mass_one hμ, one_mul]

/-! ## Inner products -/

/-- `⟨f, h⟩ = ∑_z f(z) h(z)`. -/
noncomputable def ip (f h : X → ℝ) : ℝ := ∑' z, f z * h z

lemma ip_Pop {μ : G →₀ ℝ} (hs : IsSymmetric μ) {f h : X → ℝ} (hf : FS f) (_hh : FS h) :
    ip (Pop μ f) h = ip f (Pop μ h) := by
  unfold ip Pop
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  have e1 : ∀ z, ∑ g ∈ μ.support, μ g * f (g⁻¹ • z) * h z =
      ∑ g ∈ μ.support, μ g * (f (g⁻¹ • z) * h z) := fun z =>
    Finset.sum_congr rfl fun g _ => by ring
  have e2 : ∀ z, ∑ g ∈ μ.support, f z * (μ g * h (g⁻¹ • z)) =
      ∑ g ∈ μ.support, μ g * (f z * h (g⁻¹ • z)) := fun z =>
    Finset.sum_congr rfl fun g _ => by ring
  simp_rw [e1, e2]
  rw [tsum_sum_mul _ _ _ (fun g _ => ((hf.comp_smul g⁻¹).mul_right h).summable),
    tsum_sum_mul _ _ _ (fun g _ => (hf.mul_right _).summable)]
  -- `∑_z f(g⁻¹ z) h(z) = ∑_w f(w) h(g w)`
  have e3 : ∀ g : G, ∑' z, f (g⁻¹ • z) * h z = ∑' w, f w * h (g • w) := by
    intro g
    rw [← tsum_smul_comp (fun z => f (g⁻¹ • z) * h z) g]
    simp only [inv_smul_smul]
  simp_rw [e3]
  exact (sum_inv hs (fun g => ∑' w, f w * h (g • w))).symm

/-! ## Dirichlet forms -/

/-- The Dirichlet form of `f` along `g`. -/
noncomputable def Dg (f : X → ℝ) (g : G) : ℝ := ∑' z, (f z - f (g • z)) ^ 2

/-- The bilinear Dirichlet form of `μ`. -/
noncomputable def B (μ : G →₀ ℝ) (f h : X → ℝ) : ℝ :=
  ∑ g ∈ μ.support, μ g * ∑' z, (f z - f (g • z)) * (h z - h (g • z))

lemma B_self (μ : G →₀ ℝ) (f : X → ℝ) : B μ f f = ∑ g ∈ μ.support, μ g * Dg f g := by
  unfold B Dg
  simp_rw [sq]

lemma B_neg (μ : G →₀ ℝ) (f : X → ℝ) : B μ (fun z => - f z) (fun z => - f z) = B μ f f := by
  unfold B
  refine Finset.sum_congr rfl fun g _ => ?_
  congr 1
  exact tsum_congr fun z => by ring

lemma FS.sq_diff {f : X → ℝ} (hf : FS f) (g : G) : FS (fun z => (f z - f (g • z)) ^ 2) :=
  hf.of_zero (hf.comp_smul g) (fun z h1 h2 => by simp [h1, h2])

lemma Dg_nonneg (f : X → ℝ) (g : G) : 0 ≤ Dg f g := tsum_nonneg fun _ => sq_nonneg _

lemma B_self_nonneg {μ : G →₀ ℝ} (hμ0 : ∀ g, 0 ≤ μ g) (f : X → ℝ) : 0 ≤ B μ f f := by
  rw [B_self]
  exact Finset.sum_nonneg fun g _ => mul_nonneg (hμ0 g) (Dg_nonneg f g)

lemma term_le_Dg {f : X → ℝ} (hf : FS f) (g : G) (z : X) : (f z - f (g • z)) ^ 2 ≤ Dg f g :=
  (hf.sq_diff g).summable.le_tsum z (fun _ _ => sq_nonneg _)

/-- `B(f, h) = 2 ⟨f, h - P h⟩` for symmetric probabilities. -/
lemma B_eq {μ : G →₀ ℝ} (hμ : ThompsonAmenability.IsProbability μ) (hs : IsSymmetric μ)
    {f h : X → ℝ} (hf : FS f) (_hh : FS h) :
    B μ f h = 2 * ip f h - 2 * ip f (Pop μ h) := by
  have hT : ∀ g : G, ∑' z, (f z - f (g • z)) * (h z - h (g • z)) =
      2 * ip f h - ∑' z, f z * h (g • z) - ∑' w, f w * h (g⁻¹ • w) := by
    intro g
    have h1 : HasSum (fun z => f z * h z) (ip f h) := (hf.mul_right h).summable.hasSum
    have h2 : HasSum (fun z => f (g • z) * h (g • z)) (ip f h) :=
      hasSum_smul_comp (φ := fun z => f z * h z) g h1
    have h3 : HasSum (fun z => f z * h (g • z)) (∑' z, f z * h (g • z)) :=
      (hf.mul_right _).summable.hasSum
    have h4' : HasSum (fun w => f w * h (g⁻¹ • w)) (∑' w, f w * h (g⁻¹ • w)) :=
      (hf.mul_right _).summable.hasSum
    have h4 : HasSum (fun z => f (g • z) * h z) (∑' w, f w * h (g⁻¹ • w)) := by
      have := hasSum_smul_comp (φ := fun w => f w * h (g⁻¹ • w)) g h4'
      simpa only [inv_smul_smul] using this
    have := ((h1.add h2).sub h3).sub h4
    refine (this.congr_fun ?_).tsum_eq.trans (by ring)
    intro z; ring
  unfold B
  simp_rw [hT]
  have hA : ∑ g ∈ μ.support, μ g * (2 * ip f h - ∑' z, f z * h (g • z) -
      ∑' w, f w * h (g⁻¹ • w)) = 2 * ip f h * ∑ g ∈ μ.support, μ g -
      ∑ g ∈ μ.support, μ g * (∑' z, f z * h (g⁻¹⁻¹ • z)) -
      ∑ g ∈ μ.support, μ g * ∑' w, f w * h (g⁻¹ • w) := by
    simp only [inv_inv, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun g _ => by ring
  rw [hA, sum_inv hs (fun g => ∑' z, f z * h (g⁻¹ • z)), mass_one hμ]
  have hP : ∑ g ∈ μ.support, μ g * ∑' w, f w * h (g⁻¹ • w) = ip f (Pop μ h) := by
    unfold ip Pop
    simp_rw [Finset.mul_sum]
    have e : ∀ w, ∑ g ∈ μ.support, f w * (μ g * h (g⁻¹ • w)) =
        ∑ g ∈ μ.support, μ g * (f w * h (g⁻¹ • w)) := fun w =>
      Finset.sum_congr rfl fun g _ => by ring
    simp_rw [e]
    rw [tsum_sum_mul _ _ _ (fun g _ => (hf.mul_right _).summable)]
  rw [hP]; ring

/-- AM–GM for the bilinear form. -/
lemma B_le {μ : G →₀ ℝ} (hμ0 : ∀ g, 0 ≤ μ g) {f h : X → ℝ} (hf : FS f) (hh : FS h)
    {s : ℝ} (hs : 0 < s) : B μ f h ≤ (s * B μ f f + B μ h h / s) / 2 := by
  have key : ∀ x y : ℝ, x * y ≤ (s * (x * x) + y * y / s) / 2 := by
    intro x y
    have : 0 ≤ (s * x - y) ^ 2 / s := div_nonneg (sq_nonneg _) hs.le
    have e : (s * x - y) ^ 2 / s = s * (x * x) + y * y / s - 2 * (x * y) := by
      field_simp; ring
    linarith
  unfold B
  rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_le_sum fun g _ => ?_
  have sf : Summable fun z => (f z - f (g • z)) * (f z - f (g • z)) :=
    ((hf.sub (hf.comp_smul g)).mul_right _).summable
  have sh : Summable fun z => (h z - h (g • z)) * (h z - h (g • z)) :=
    ((hh.sub (hh.comp_smul g)).mul_right _).summable
  have sfh : Summable fun z => (f z - f (g • z)) * (h z - h (g • z)) :=
    ((hf.sub (hf.comp_smul g)).mul_right _).summable
  have hle : ∑' z, (f z - f (g • z)) * (h z - h (g • z)) ≤
      (s * ∑' z, (f z - f (g • z)) * (f z - f (g • z)) +
        (∑' z, (h z - h (g • z)) * (h z - h (g • z))) / s) / 2 := by
    rw [← tsum_mul_left, ← tsum_div_const, ← Summable.tsum_add (sf.mul_left s) (sh.div_const s),
      ← tsum_div_const]
    exact Summable.tsum_le_tsum (fun z => key _ _) sfh (((sf.mul_left s).add
      (sh.div_const s)).div_const 2)
  have := mul_le_mul_of_nonneg_left hle (hμ0 g)
  calc μ g * ∑' z, (f z - f (g • z)) * (h z - h (g • z))
      ≤ μ g * ((s * ∑' z, (f z - f (g • z)) * (f z - f (g • z)) +
        (∑' z, (h z - h (g • z)) * (h z - h (g • z))) / s) / 2) := this
    _ = _ := by ring

lemma ip_le {f h : X → ℝ} (hf : FS f) (hh : FS h) {t : ℝ} (ht : 0 < t) :
    ip f h ≤ (t * ip f f + ip h h / t) / 2 := by
  have key : ∀ x y : ℝ, x * y ≤ (t * (x * x) + y * y / t) / 2 := by
    intro x y
    have : 0 ≤ (t * x - y) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
    have e : (t * x - y) ^ 2 / t = t * (x * x) + y * y / t - 2 * (x * y) := by
      field_simp; ring
    linarith
  have sf : Summable fun z => f z * f z := (hf.mul_right _).summable
  have sh : Summable fun z => h z * h z := (hh.mul_right _).summable
  unfold ip
  rw [← tsum_mul_left, ← tsum_div_const, ← Summable.tsum_add (sf.mul_left t) (sh.div_const t),
    ← tsum_div_const]
  exact Summable.tsum_le_tsum (fun z => key _ _) (hf.mul_right _).summable
    (((sf.mul_left t).add (sh.div_const t)).div_const 2)

/-! ## Comparison of Dirichlet forms -/

lemma Dg_one (f : X → ℝ) : Dg f (1 : G) = 0 := by
  simp [Dg]

lemma Dg_inv (f : X → ℝ) (g : G) : Dg f g⁻¹ = Dg f g := by
  unfold Dg
  rw [← tsum_smul_comp (fun z => (f z - f (g⁻¹ • z)) ^ 2) g]
  refine tsum_congr fun z => ?_
  simp only [inv_smul_smul]
  ring

lemma Dg_mul {f : X → ℝ} (hf : FS f) (g h : G) : Dg f (g * h) ≤ 2 * Dg f g + 2 * Dg f h := by
  have hs1 := (hf.sq_diff h).summable
  have hs2 : Summable fun z => (f (h • z) - f (g • (h • z))) ^ 2 :=
    ((hf.comp_smul h).of_zero ((hf.comp_smul g).comp_smul h)
      (fun z h1 h2 => by simp [h1, h2])).summable
  have key : Dg f g = ∑' z, (f (h • z) - f (g • (h • z))) ^ 2 :=
    (tsum_smul_comp (fun w => (f w - f (g • w)) ^ 2) h).symm
  have hle : ∀ z, (f z - f ((g * h) • z)) ^ 2 ≤
      2 * (f (h • z) - f (g • (h • z))) ^ 2 + 2 * (f z - f (h • z)) ^ 2 := by
    intro z
    rw [mul_smul]
    nlinarith [sq_nonneg ((f z - f (h • z)) - (f (h • z) - f (g • (h • z))))]
  calc Dg f (g * h) ≤ ∑' z, (2 * (f (h • z) - f (g • (h • z))) ^ 2
        + 2 * (f z - f (h • z)) ^ 2) :=
        Summable.tsum_le_tsum hle (hf.sq_diff (g * h)).summable
          ((hs2.mul_left 2).add (hs1.mul_left 2))
    _ = 2 * Dg f g + 2 * Dg f h := by
        rw [Summable.tsum_add (hs2.mul_left 2) (hs1.mul_left 2), tsum_mul_left,
          tsum_mul_left, key, Dg]

lemma Dg_le_B {μ : G →₀ ℝ} (hμ0 : ∀ g, 0 ≤ μ g) (hnd : IsNondegenerate μ) (g : G) :
    ∃ C, 0 ≤ C ∧ ∀ f : X → ℝ, FS f → Dg f g ≤ C * B μ f f := by
  have hg : g ∈ Subgroup.closure (μ.support : Set G) := by
    rw [show Subgroup.closure (μ.support : Set G) = ⊤ from hnd]; trivial
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    have hx' : x ∈ μ.support := hx
    have hpos : 0 < μ x := lt_of_le_of_ne (hμ0 x) (Ne.symm (Finsupp.mem_support_iff.mp hx'))
    refine ⟨1 / μ x, by positivity, fun f _ => ?_⟩
    have : μ x * Dg f x ≤ B μ f f := by
      rw [B_self]
      exact Finset.single_le_sum (f := fun h => μ h * Dg f h)
        (fun h _ => mul_nonneg (hμ0 h) (Dg_nonneg f h)) hx'
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos]
    linarith
  | one => exact ⟨0, le_rfl, fun f _ => by rw [Dg_one, zero_mul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨Cx, hCx, hx⟩ := hx
    obtain ⟨Cy, hCy, hy⟩ := hy
    refine ⟨2 * Cx + 2 * Cy, by positivity, fun f hf => ?_⟩
    have := Dg_mul hf x y
    have h1 := hx f hf
    have h2 := hy f hf
    nlinarith
  | inv x _ hx =>
    obtain ⟨C, hC, hx⟩ := hx
    exact ⟨C, hC, fun f hf => by rw [Dg_inv]; exact hx f hf⟩

lemma B_le_B {μ ν : G →₀ ℝ} (hμ0 : ∀ g, 0 ≤ μ g) (hν0 : ∀ g, 0 ≤ ν g)
    (hnd : IsNondegenerate μ) :
    ∃ K, 0 ≤ K ∧ ∀ f : X → ℝ, FS f → B ν f f ≤ K * B μ f f := by
  choose C hC0 hC using fun g : G => Dg_le_B (X := X) hμ0 hnd g
  refine ⟨∑ h ∈ ν.support, ν h * C h,
    Finset.sum_nonneg fun h _ => mul_nonneg (hν0 h) (hC0 h), fun f hf => ?_⟩
  rw [B_self, Finset.sum_mul]
  refine Finset.sum_le_sum fun h _ => ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC h f hf) (hν0 h)

/-! ## The chain: laws, killed laws, first returns -/

section Chain

variable (μ : G →₀ ℝ) (o : X)

/-- The law of the chain at time `n`, started at `o`. -/
noncomputable def p : ℕ → X → ℝ
  | 0 => fun z => if z = o then 1 else 0
  | n + 1 => Pop μ (p n)

/-- The law at time `n` of the chain killed at its first return to `o`. -/
noncomputable def a : ℕ → X → ℝ
  | 0 => fun z => if z = o then 1 else 0
  | n + 1 => fun z => if z = o then 0 else Pop μ (a n) z

/-- The probability of a first return at time `n + 1`. -/
noncomputable def fr (n : ℕ) : ℝ := Pop μ (a μ o n) o

/-- The truncated Green function `u_N = ∑_{n<N} p_n`. -/
noncomputable def u (N : ℕ) (z : X) : ℝ := ∑ n ∈ Finset.range N, p μ o n z

variable {μ o}

lemma p_FS (n : ℕ) : FS (p μ o n) := by
  induction n with
  | zero => exact FS.delta o
  | succ n ih => exact Pop_FS μ ih

lemma a_FS (n : ℕ) : FS (a μ o n) := by
  induction n with
  | zero => exact FS.delta o
  | succ n ih =>
    exact (Pop_FS μ ih).of_zero (Pop_FS μ ih) (fun z h _ => by simp [a, h])

lemma u_FS (N : ℕ) : FS (u μ o N) := FS.finset_sum _ fun n => p_FS n

lemma p_nonneg (hμ0 : ∀ g, 0 ≤ μ g) (n : ℕ) (z : X) : 0 ≤ p μ o n z := by
  induction n generalizing z with
  | zero => simp only [p]; split_ifs <;> norm_num
  | succ n ih => exact Pop_nonneg hμ0 ih z

lemma a_nonneg (hμ0 : ∀ g, 0 ≤ μ g) (n : ℕ) (z : X) : 0 ≤ a μ o n z := by
  induction n generalizing z with
  | zero => simp only [a]; split_ifs <;> norm_num
  | succ n ih =>
    simp only [a]
    split_ifs
    · exact le_rfl
    · exact Pop_nonneg hμ0 ih z

lemma fr_nonneg (hμ0 : ∀ g, 0 ≤ μ g) (n : ℕ) : 0 ≤ fr μ o n :=
  Pop_nonneg hμ0 (a_nonneg hμ0 n) o

lemma u_nonneg (hμ0 : ∀ g, 0 ≤ μ g) (N : ℕ) (z : X) : 0 ≤ u μ o N z :=
  Finset.sum_nonneg fun n _ => p_nonneg hμ0 n z

/-! ### Identification with `firstReturnProb` -/

lemma walkKernel_eq (x y : X) :
    walkKernel (μ : G → ℝ) x y = ∑ g ∈ μ.support, if g • x = y then μ g else 0 := by
  unfold walkKernel
  rw [tsum_eq_sum (s := μ.support)]
  intro g hg
  split_ifs
  · exact Finsupp.notMem_support_iff.1 hg
  · rfl

lemma tsum_kernel (f : X → ℝ) (z : X) :
    ∑' x, f x * walkKernel (μ : G → ℝ) x z = Pop μ f z := by
  simp_rw [walkKernel_eq, Finset.mul_sum]
  have hz : ∀ g : G, ∀ x, x ≠ g⁻¹ • z → f x * (if g • x = z then μ g else 0) = 0 := by
    intro g x hx
    rw [if_neg, mul_zero]
    intro e; apply hx; rw [← e, inv_smul_smul]
  rw [Summable.tsum_finsetSum (fun g _ => (hasSum_single _ (hz g)).summable)]
  unfold Pop
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [tsum_eq_single _ (hz g), if_pos (smul_inv_smul g z), mul_comm]

lemma Pop_delta (y : X) : Pop μ (p μ o 0) y = walkKernel (μ : G → ℝ) o y := by
  rw [← tsum_kernel]
  rw [tsum_eq_single o]
  · simp [p]
  · intro x hx; simp [p, hx]

lemma avoidProb_eq (n : ℕ) :
    avoidProb (walkKernel (μ : G → ℝ)) o (n + 1) = a μ o (n + 1) := by
  induction n with
  | zero =>
    funext y
    simp only [avoidProb, a]
    rw [← Pop_delta]
    rfl
  | succ n ih =>
    funext y
    simp only [avoidProb]
    simp_rw [ih, tsum_kernel]
    rfl

lemma firstReturnProb_eq (n : ℕ) :
    firstReturnProb (walkKernel (μ : G → ℝ)) o n = fr μ o n := by
  cases n with
  | zero =>
    simp only [firstReturnProb, fr]
    rw [← Pop_delta]
    rfl
  | succ n =>
    simp only [firstReturnProb, fr]
    rw [avoidProb_eq, tsum_kernel]

/-! ### First returns sum to at most `1` -/

lemma fr_partial (hμ : ThompsonAmenability.IsProbability μ) (n : ℕ) :
    ∑ k ∈ Finset.range n, fr μ o k + ∑' z, a μ o n z = 1 := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add, a]
    exact tsum_ite_eq o (fun _ => (1 : ℝ))
  | succ n ih =>
    have hs := (Pop_FS μ (a_FS (μ := μ) (o := o) n)).summable
    have e : ∑' z, a μ o (n + 1) z = ∑' z, a μ o n z - fr μ o n := by
      rw [← tsum_Pop hμ (a_FS n), hs.tsum_eq_add_tsum_ite o]
      simp only [a, fr]
      ring
    rw [Finset.sum_range_succ, e]
    linarith

lemma fr_sum_le (hμ : ThompsonAmenability.IsProbability μ) (n : ℕ) :
    ∑ k ∈ Finset.range n, fr μ o k ≤ 1 := by
  have := fr_partial (o := o) hμ n
  have : 0 ≤ ∑' z, a μ o n z := tsum_nonneg (a_nonneg hμ.1 n)
  linarith

lemma fr_summable (hμ : ThompsonAmenability.IsProbability μ) : Summable (fr μ o) :=
  summable_of_sum_range_le (fr_nonneg hμ.1) (fr_sum_le hμ)

/-! ### Renewal -/

lemma renewal (n : ℕ) (z : X) :
    p μ o (n + 1) z = a μ o (n + 1) z +
      ∑ k ∈ Finset.range (n + 1), fr μ o k * p μ o (n - k) z := by
  induction n generalizing z with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_zero]
    show Pop μ (p μ o 0) z = (if z = o then 0 else Pop μ (a μ o 0) z) + fr μ o 0 * p μ o 0 z
    simp only [fr]
    have h0 : a μ o 0 = p μ o 0 := rfl
    rw [h0]
    by_cases hz : z = o
    · subst hz; simp [p]
    · simp [p, hz]
  | succ n ih =>
    have step : p μ o (n + 2) z = Pop μ (a μ o (n + 1)) z +
        ∑ k ∈ Finset.range (n + 1), fr μ o k * p μ o (n + 1 - k) z := by
      show Pop μ (p μ o (n + 1)) z = _
      have : p μ o (n + 1) = fun w => a μ o (n + 1) w +
          ∑ k ∈ Finset.range (n + 1), fr μ o k * p μ o (n - k) w := funext ih
      rw [this]
      unfold Pop
      simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < n + 1 := Finset.mem_range.1 hk
      rw [show n + 1 - k = (n - k) + 1 by omega]
      show _ = fr μ o k * Pop μ (p μ o (n - k)) z
      unfold Pop
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun g _ => by ring
    rw [step, Finset.sum_range_succ _ (n + 1), Nat.sub_self]
    by_cases hz : z = o
    · subst hz
      simp only [a, p, fr, if_true]
      ring
    · simp only [a, p, hz, if_false]
      ring

lemma u_succ (N : ℕ) :
    u μ o (N + 1) o = 1 + ∑ k ∈ Finset.range N, fr μ o k * u μ o (N - k) o := by
  unfold u
  rw [Finset.sum_range_succ']
  have h0 : p μ o 0 o = 1 := by simp [p]
  rw [h0, add_comm]
  congr 1
  have : ∀ n, p μ o (n + 1) o = ∑ k ∈ Finset.range (n + 1), fr μ o k * p μ o (n - k) o := by
    intro n
    rw [renewal]
    simp [a]
  simp_rw [this]
  rw [Finset.sum_range_diag_flip N (fun k m => fr μ o k * p μ o m o)]
  simp_rw [Finset.mul_sum]

lemma u_mono (hμ0 : ∀ g, 0 ≤ μ g) : Monotone fun N => u μ o N o := by
  refine monotone_nat_of_le_succ fun N => ?_
  show u μ o N o ≤ u μ o (N + 1) o
  unfold u
  rw [Finset.sum_range_succ]
  linarith [p_nonneg (o := o) hμ0 N o]

/-- Transience bounds the Green function. -/
lemma u_bdd (hμ : ThompsonAmenability.IsProbability μ) (hF : ∑' k, fr μ o k < 1) (N : ℕ) :
    u μ o N o ≤ 1 / (1 - ∑' k, fr μ o k) := by
  set F := ∑' k, fr μ o k
  set M := 1 / (1 - F)
  have hne : 1 - F ≠ 0 := by linarith
  have hM : 1 + F * M = M := by
    simp only [M]; field_simp; ring
  have hM0 : 0 ≤ M := by simp only [M]; exact div_nonneg zero_le_one (by linarith)
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    cases N with
    | zero => simp [u, hM0]
    | succ N =>
      rw [u_succ]
      have h1 : ∑ k ∈ Finset.range N, fr μ o k * u μ o (N - k) o ≤
          ∑ k ∈ Finset.range N, fr μ o k * M :=
        Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (ih _ (by omega)) (fr_nonneg hμ.1 k)
      have h2 : ∑ k ∈ Finset.range N, fr μ o k ≤ F :=
        (fr_summable hμ).sum_le_tsum _ (fun k _ => fr_nonneg hμ.1 k)
      rw [← Finset.sum_mul] at h1
      nlinarith

/-- Recurrence makes the Green function unbounded. -/
lemma not_bdd (hμ : ThompsonAmenability.IsProbability μ) (hrec : HasSum (fr μ o) 1) (M : ℝ)
    (hM : ∀ N, u μ o N o ≤ M) : False := by
  have hbdd : BddAbove (Set.range fun N => u μ o N o) := ⟨M, by rintro _ ⟨N, rfl⟩; exact hM N⟩
  set S := ⨆ N, u μ o N o
  have hle : ∀ N, u μ o N o ≤ S := fun N => le_ciSup hbdd N
  have hS1 : 1 ≤ S := by
    have := hle 1
    simp [u, p] at this
    exact this
  have hK : ∀ K, 1 + (∑ k ∈ Finset.range K, fr μ o k) * S ≤ S := by
    intro K
    set FK := ∑ k ∈ Finset.range K, fr μ o k
    have hFK : 0 ≤ FK := Finset.sum_nonneg fun k _ => fr_nonneg hμ.1 k
    have hJ : ∀ J, FK * u μ o J o ≤ S - 1 := by
      intro J
      have e := u_succ (μ := μ) (o := o) (J + K)
      have h1 : FK * u μ o J o ≤ ∑ k ∈ Finset.range K, fr μ o k * u μ o (J + K - k) o := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left
          (u_mono hμ.1 (by have := Finset.mem_range.1 hk; omega)) (fr_nonneg hμ.1 k)
      have h2 : ∑ k ∈ Finset.range K, fr μ o k * u μ o (J + K - k) o ≤
          ∑ k ∈ Finset.range (J + K), fr μ o k * u μ o (J + K - k) o :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          (fun k _ _ => mul_nonneg (fr_nonneg hμ.1 k) (u_nonneg hμ.1 _ o))
      have h3 := hle (J + K + 1)
      linarith
    have : FK * S ≤ S - 1 := by
      rw [Real.mul_iSup_of_nonneg hFK]
      exact ciSup_le hJ
    linarith
  have ht : Filter.Tendsto (fun K => 1 + (∑ k ∈ Finset.range K, fr μ o k) * S) Filter.atTop
      (nhds (1 + 1 * S)) :=
    tendsto_const_nhds.add (hrec.tendsto_sum_nat.mul tendsto_const_nhds)
  have := le_of_tendsto' ht hK
  linarith

/-! ### Energy of the truncated Green function -/

lemma u_sub_Pop (N : ℕ) (z : X) :
    u μ o N z - Pop μ (u μ o N) z = p μ o 0 z - p μ o N z := by
  unfold u
  rw [Pop_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_range_sub' (fun n => p μ o n z) N

lemma ip_delta (f : X → ℝ) : ip f (p μ o 0) = f o := by
  unfold ip
  simp only [p, mul_ite, mul_one, mul_zero]
  exact tsum_ite_eq o f

lemma ip_u_sub {f : X → ℝ} (_hf : FS f) (N : ℕ) :
    ip f (u μ o N) - ip f (Pop μ (u μ o N)) = f o - ip f (p μ o N) := by
  unfold ip
  rw [← Summable.tsum_sub ((u_FS N).mul_left f).summable
    ((Pop_FS μ (u_FS N)).mul_left f).summable]
  have : ∀ z, f z * u μ o N z - f z * Pop μ (u μ o N) z =
      f z * p μ o 0 z - f z * p μ o N z := by
    intro z; rw [← mul_sub, ← mul_sub, u_sub_Pop]
  simp_rw [this]
  rw [Summable.tsum_sub ((p_FS 0).mul_left f).summable ((p_FS N).mul_left f).summable]
  have := ip_delta (μ := μ) (o := o) f
  unfold ip at this
  rw [this]

lemma B_u_le (hμ : ThompsonAmenability.IsProbability μ) (hs : IsSymmetric μ) (N : ℕ) :
    B μ (u μ o N) (u μ o N) ≤ 2 * u μ o N o := by
  rw [B_eq hμ hs (u_FS N) (u_FS N)]
  have e := ip_u_sub (μ := μ) (o := o) (u_FS (μ := μ) (o := o) N) N
  have : 0 ≤ ip (u μ o N) (p μ o N) :=
    tsum_nonneg fun z => mul_nonneg (u_nonneg hμ.1 N z) (p_nonneg hμ.1 N z)
  linarith

lemma ip_p (hs : IsSymmetric μ) (m n : ℕ) : ip (p μ o m) (p μ o n) = p μ o (m + n) o := by
  induction m generalizing n with
  | zero =>
    unfold ip
    simp only [p, ite_mul, one_mul, zero_mul, zero_add]
    exact tsum_ite_eq o _
  | succ m ih =>
    show ip (Pop μ (p μ o m)) (p μ o n) = _
    rw [ip_Pop hs (p_FS m) (p_FS n)]
    rw [show m + 1 + n = m + (n + 1) by omega]
    exact ih (n + 1)

end Chain

/-! ## Hardy inequality from a bounded Green function -/

/-- From `|x| ≤ s E / 4 + M / (2 s)` for all `s > 0`, `x² ≤ (M/2) E`. -/
lemma sq_le_of_forall {x M E : ℝ} (hM1 : 1 ≤ M) (hE : 0 ≤ E)
    (two : ∀ s : ℝ, 0 < s → |x| ≤ s * E / 4 + M / (2 * s)) : x ^ 2 ≤ M / 2 * E := by
  set v := |x|
  have hv : x ^ 2 = v ^ 2 := (sq_abs _).symm
  rw [hv]
  rcases (abs_nonneg x).lt_or_eq with hv0 | hv0
  · rcases hE.lt_or_eq with hE0 | hE0
    · have := two (2 * v / E) (by positivity)
      have e : 2 * v / E * E / 4 = v / 2 := by field_simp; ring
      have e' : M / (2 * (2 * v / E)) = M * E / (4 * v) := by field_simp; ring
      rw [e, e'] at this
      have h' : v / 2 ≤ M * E / (4 * v) := by linarith
      rw [le_div_iff₀ (by positivity)] at h'
      nlinarith
    · have := two (2 * M / v) (by positivity)
      rw [← hE0] at this
      have e : M / (2 * (2 * M / v)) = v / 4 := by field_simp; ring
      rw [e] at this
      linarith
  · have h0 : v = 0 := hv0.symm
    rw [h0]
    have : (0:ℝ) ^ 2 = 0 := by norm_num
    rw [this]
    exact mul_nonneg (by linarith) hE

lemma hardy_of_bdd {ν : G →₀ ℝ} (hν : ThompsonAmenability.IsProbability ν) (hs : IsSymmetric ν)
    (o : X) (M : ℝ) (hM : ∀ N, u ν o N o ≤ M) :
    ∃ C, 0 ≤ C ∧ ∀ f : X → ℝ, FS f → f o ^ 2 ≤ C * B ν f f := by
  have hM1 : 1 ≤ M := by
    have := hM 1
    simp [u, p] at this
    exact this
  -- `p_{2N}(o) → 0`
  have hsum : Summable fun n => p ν o n o :=
    summable_of_sum_range_le (fun n => p_nonneg hν.1 n o) (fun n => by
      have := hM n
      unfold u at this
      exact this)
  have hlim : Filter.Tendsto (fun N => p ν o (N + N) o) Filter.atTop (nhds 0) :=
    hsum.tendsto_atTop_zero.comp (f := fun N : ℕ => N + N)
      (Filter.tendsto_atTop_mono (fun n => Nat.le_add_right n n) Filter.tendsto_id)
  -- one-sided bound
  have one : ∀ f : X → ℝ, FS f → ∀ s : ℝ, 0 < s → f o ≤ s * B ν f f / 4 + M / (2 * s) := by
    intro f hf s hs0
    have hN : ∀ N, ∀ t : ℝ, 0 < t → f o ≤ s * B ν f f / 4 + M / (2 * s) +
        (t * ip f f + p ν o (N + N) o / t) / 2 := by
      intro N t ht
      have e1 := ip_u_sub (μ := ν) (o := o) hf N
      have e2 := B_eq hν hs hf (u_FS (μ := ν) (o := o) N)
      have e3 := B_le hν.1 hf (u_FS (μ := ν) (o := o) N) hs0
      have e4 := B_u_le (o := o) hν hs N
      have e5 := ip_le hf (p_FS (μ := ν) (o := o) N) ht
      rw [ip_p hs] at e5
      have e6 : B ν (u ν o N) (u ν o N) / s ≤ 2 * M / s :=
        div_le_div_of_nonneg_right (by linarith [hM N]) hs0.le
      have e7 : 2 * M / s = 4 * (M / (2 * s)) := by field_simp; ring
      linarith
    have hT : ∀ t : ℝ, 0 < t → f o ≤ s * B ν f f / 4 + M / (2 * s) + t * ip f f / 2 := by
      intro t ht
      have hc : Filter.Tendsto (fun N => s * B ν f f / 4 + M / (2 * s) +
          (t * ip f f + p ν o (N + N) o / t) / 2) Filter.atTop
          (nhds (s * B ν f f / 4 + M / (2 * s) + (t * ip f f + 0 / t) / 2)) :=
        tendsto_const_nhds.add ((tendsto_const_nhds.add (hlim.div_const t)).div_const 2)
      have := ge_of_tendsto' hc (fun N => hN N t ht)
      rw [zero_div, add_zero] at this
      linarith
    have hff : 0 ≤ ip f f := tsum_nonneg fun z => mul_self_nonneg (f z)
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have := hT (ε / (ip f f + 1)) (by positivity)
    have h2 : ε / (ip f f + 1) * ip f f / 2 < ε := by
      rw [div_mul_eq_mul_div, div_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  refine ⟨M / 2, by linarith, fun f hf => ?_⟩
  have hE : 0 ≤ B ν f f := B_self_nonneg hν.1 f
  refine sq_le_of_forall hM1 hE fun s hs0 => ?_
  rcases abs_cases (f o) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; exact one f hf s hs0
  · rw [h]
    have := one (fun z => - f z) hf.neg s hs0
    rwa [B_neg] at this

/-! ## The comparison theorem -/

theorem isRecurrentChain_comparison {G X : Type*} [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X] (μ : G →₀ ℝ) (hμ : ThompsonAmenability.IsProbability μ)
    (hsymm : IsSymmetric μ) (hnd : IsNondegenerate μ) (x₀ : X)
    (hrec : IsRecurrentChain (walkKernel (μ : G → ℝ)) x₀)
    (ν : G →₀ ℝ) (hν : ThompsonAmenability.IsProbability ν) (hνsymm : IsSymmetric ν) (y : X) :
    IsRecurrentChain (walkKernel (ν : G → ℝ)) y := by
  by_contra hnot
  unfold IsRecurrentChain at hrec hnot
  have efr : ∀ (κ : G →₀ ℝ) (o : X), firstReturnProb (walkKernel (κ : G → ℝ)) o = fr κ o :=
    fun κ o => funext fun n => firstReturnProb_eq n
  rw [efr] at hrec hnot
  -- `ν` is transient at `y`: its Green function is bounded
  have hsν := fr_summable (o := y) hν
  have hle1 : ∑' k, fr ν y k ≤ 1 :=
    Real.tsum_le_of_sum_range_le (fr_nonneg hν.1) (fr_sum_le hν)
  have hlt : ∑' k, fr ν y k < 1 := by
    rcases hle1.lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ hsν.hasSum) hnot
  -- Hardy inequality for `ν` at `y`
  obtain ⟨C1, hC1, hH1⟩ := hardy_of_bdd hν hνsymm y _ (u_bdd hν hlt)
  -- comparison of Dirichlet forms
  obtain ⟨K, hK, hBK⟩ := B_le_B (X := X) hμ.1 hν.1 hnd
  -- move the base point
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G y x₀
  obtain ⟨C2, hC2, hD⟩ := Dg_le_B (X := X) hμ.1 hnd g
  have hH : ∀ f : X → ℝ, FS f → f x₀ ^ 2 ≤ (2 * C1 * K + 2 * C2) * B μ f f := by
    intro f hf
    have h1 := hH1 f hf
    have h2 := hBK f hf
    have h3 := term_le_Dg hf g y
    have h4 := hD f hf
    rw [hg] at h3
    have hB := B_self_nonneg hμ.1 f
    have hBν := B_self_nonneg hν.1 f
    nlinarith [sq_nonneg (f y + (f y - f x₀)), mul_le_mul_of_nonneg_left h2 hC1]
  -- the Green function of `μ` at `x₀` is bounded
  set C := 2 * C1 * K + 2 * C2
  have hC : 0 ≤ C := by positivity
  apply not_bdd hμ hrec (2 * C)
  intro N
  have h1 := hH (u μ x₀ N) (u_FS N)
  have h2 := B_u_le (o := x₀) hμ hsymm N
  have h0 := u_nonneg (o := x₀) hμ.1 N x₀
  nlinarith [mul_le_mul_of_nonneg_left h2 hC]

end JMMS.IETRC
end

section

/-! # JMMS Lemma 4.3 (Bartholdi–Erschler): recurrence and inverted orbits

`JMMS.IETP43.isRecurrentChain_iff`: for any symmetric finitely
supported probability `μ` and any `x₀`, the `μ`-chain is recurrent at `x₀` iff
`(1/n) E|O_n| → 0`. The route is the paper's: `E|O_{n+1}| - E|O_n| = P(T > n + 1)` by reversing
and inverting the steps, `P(T > N) = 1 - ∑_{j<N} firstReturnProb j`, then Cesàro.

The converse also needs that recurrence for `(μ, x₀)` gives recurrence for every symmetric
finitely supported `ν` and every base point: `JMMS.IETP43.isRecurrentChain_comparison`, proved by
a Dirichlet-form comparison in `JMMS.IETRC` above. -/

open IntervalExchange

set_option linter.unusedSectionVars false

namespace JMMS.IETP43

variable {G X : Type*} [Group G] [MulAction G X]

/-! ## The left random walk as a list product -/

lemma filter_finRange_lt (n k : ℕ) :
    (List.finRange n).filter (fun i : Fin n => decide (i.val < k)) = (List.finRange n).take k := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ]
    cases k with
    | zero =>
      simp only [List.take_zero]
      rw [List.filter_eq_nil_iff]
      intro a _
      simp
    | succ k =>
      rw [List.filter_cons_of_pos (by simp), List.take_succ_cons]
      congr 1
      rw [List.filter_map, ← List.map_take, ← ih k]
      congr 1
      apply List.filter_congr
      intro i _
      simp [Fin.val_succ]

lemma walkPos_eq {n : ℕ} (h : Fin n → G) (k : ℕ) :
    walkPos h k = ((List.ofFn h).take k).reverse.prod := by
  unfold walkPos
  rw [filter_finRange_lt, List.ofFn_eq_map, List.map_take]

lemma walkPos_zero {n : ℕ} (h : Fin n → G) : walkPos h 0 = 1 := by
  simp [walkPos_eq]

/-- The first `N` positions of the walk only see the first `N` steps. -/
lemma walkPos_init {N : ℕ} (h : Fin (N + 1) → G) {k : ℕ} (hk : k ≤ N) :
    walkPos h k = walkPos (Fin.init h) k := by
  rw [walkPos_eq, walkPos_eq, List.ofFn_succ', List.concat_eq_append,
    List.take_append_of_le_length (by simpa using hk)]
  rfl

lemma walkPos_last {N : ℕ} (h : Fin (N + 1) → G) :
    walkPos h (N + 1) = h (Fin.last N) * walkPos (Fin.init h) N := by
  rw [walkPos_eq, walkPos_eq, List.ofFn_succ', List.concat_eq_append,
    List.take_of_length_le (by simp), List.take_of_length_le (by simp)]
  simp
  rfl

lemma ofFn_rev {α : Type*} {n : ℕ} (f : Fin n → α) :
    List.ofFn (fun j => f (Fin.rev j)) = (List.ofFn f).reverse := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_ofFn, List.getElem_reverse, List.length_ofFn]
  congr 1
  ext
  simp [Fin.val_rev]
  omega

/-- The reversed, inverted steps. -/
def revStep {n : ℕ} (h : Fin n → G) : Fin n → G := fun j => (h (Fin.rev j))⁻¹

lemma walkPos_mul_inv {n : ℕ} (h : Fin n → G) {k : ℕ} (hk : k ≤ n) :
    walkPos h k * (walkPos h n)⁻¹ = walkPos (revStep h) (n - k) := by
  have hL : (List.ofFn (revStep h)) = ((List.ofFn h).map (·⁻¹)).reverse := by
    rw [List.map_ofFn, ← ofFn_rev]
    rfl
  have hn : walkPos h n = (List.ofFn h).reverse.prod := by
    rw [walkPos_eq, List.take_of_length_le (by simp)]
  rw [hn, walkPos_eq, walkPos_eq, hL, List.take_reverse, List.reverse_reverse]
  have hlen : ((List.ofFn h).map (·⁻¹)).length - (n - k) = k := by simp; omega
  rw [hlen]
  have hsplit : (List.ofFn h).reverse.prod =
      (List.drop k (List.ofFn h)).reverse.prod * (List.take k (List.ofFn h)).reverse.prod := by
    conv_lhs => rw [← List.take_append_drop k (List.ofFn h)]
    rw [List.reverse_append, List.prod_append]
  rw [hsplit, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul,
    List.prod_inv_reverse, List.map_reverse, List.reverse_reverse, List.map_drop]

/-! ## Expectations as finite sums -/

section Exp

variable (μ : G →₀ ℝ)

/-- The weight `∏ μ(h_i)` of a step sequence. -/
noncomputable def wt {n : ℕ} (h : Fin n → G) : ℝ := ∏ i, μ (h i)

/-- `walkExp` written as a finite sum over step sequences in the support of `μ`. -/
noncomputable def E (n : ℕ) (F : (Fin n → G) → ℝ) : ℝ :=
  ∑ h : Fin n → μ.support, wt μ (fun i => (h i : G)) * F (fun i => (h i : G))

lemma walkExp_eq (n : ℕ) (F : (Fin n → G) → ℝ) : walkExp (μ : G → ℝ) n F = E μ n F := by
  unfold walkExp E wt
  rw [tsum_eq_sum (s := Finset.univ.map ⟨fun (h : Fin n → μ.support) i => (h i : G),
    fun h₁ h₂ e => funext fun i => Subtype.ext (congrFun e i)⟩)]
  · rw [Finset.sum_map]; rfl
  · intro h hh
    have : ∃ i, h i ∉ μ.support := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact hh (Finset.mem_map.2 ⟨fun i => ⟨h i, hc i⟩, Finset.mem_univ _, rfl⟩)
    obtain ⟨i, hi⟩ := this
    have h0 : μ (h i) = 0 := Finsupp.notMem_support_iff.1 hi
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, zero_mul]

variable {μ}

lemma E_congr {n : ℕ} {F F' : (Fin n → G) → ℝ} (hF : ∀ h, F h = F' h) :
    E μ n F = E μ n F' := by
  unfold E; simp only [hF]

lemma E_sub {n : ℕ} (F F' : (Fin n → G) → ℝ) :
    E μ n (fun h => F h - F' h) = E μ n F - E μ n F' := by
  unfold E; rw [← Finset.sum_sub_distrib]; simp only [mul_sub]

lemma E_add {n : ℕ} (F F' : (Fin n → G) → ℝ) :
    E μ n (fun h => F h + F' h) = E μ n F + E μ n F' := by
  unfold E; rw [← Finset.sum_add_distrib]; simp only [mul_add]

lemma wt_nonneg (hμ : ∀ g, 0 ≤ μ g) {n : ℕ} (h : Fin n → G) : 0 ≤ wt μ h :=
  Finset.prod_nonneg fun _ _ => hμ _

lemma E_nonneg (hμ : ∀ g, 0 ≤ μ g) {n : ℕ} {F : (Fin n → G) → ℝ} (hF : ∀ h, 0 ≤ F h) :
    0 ≤ E μ n F :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (wt_nonneg hμ _) (hF _)

lemma E_zero (F : (Fin 0 → G) → ℝ) : E μ 0 F = F Fin.elim0 := by
  unfold E wt
  rw [Fintype.sum_unique]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
  congr 1
  funext i; exact i.elim0

lemma sum_mu (hμ : ThompsonAmenability.IsProbability μ) : ∑ g : μ.support, μ g = 1 := by
  rw [Finset.sum_coe_sort μ.support (fun g => μ g)]
  exact hμ.2

lemma wt_snoc {n : ℕ} (q : Fin n → G) (g : G) : wt μ (Fin.snoc q g : Fin (n + 1) → G) =
    wt μ q * μ g := by
  unfold wt
  rw [Fin.prod_univ_castSucc]
  simp

lemma E_succ (n : ℕ) (F : (Fin (n + 1) → G) → ℝ) :
    E μ (n + 1) F = E μ n (fun h => ∑ g : μ.support, μ g * F (Fin.snoc h (g : G))) := by
  unfold E
  rw [← (Fin.snocEquiv fun _ => μ.support).sum_comp, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun h' _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  have hc : (fun i => ((Fin.snocEquiv (fun _ => μ.support) (g, h') i : μ.support) : G)) =
      Fin.snoc (fun i => (h' i : G)) (g : G) := by
    show (fun i => ((Fin.snoc (α := fun _ => μ.support) h' g i : μ.support) : G)) = _
    exact Fin.comp_snoc (fun x : μ.support => (x : G)) h' g
  rw [hc, wt_snoc]
  ring

lemma E_init (hμ : ThompsonAmenability.IsProbability μ) (n : ℕ) (F : (Fin n → G) → ℝ) :
    E μ (n + 1) (fun h => F (Fin.init h)) = E μ n F := by
  rw [E_succ]
  refine E_congr fun h => ?_
  simp only [Fin.init_snoc]
  rw [← Finset.sum_mul, sum_mu hμ, one_mul]

lemma E_rev (hsymm : IsSymmetric μ) (n : ℕ) (F : (Fin n → G) → ℝ) :
    E μ n (fun h => F (revStep h)) = E μ n F := by
  have hmem : ∀ x : μ.support, (x : G)⁻¹ ∈ μ.support := by
    intro x
    rw [Finsupp.mem_support_iff, hsymm]
    exact Finsupp.mem_support_iff.1 x.2
  let r : (Fin n → μ.support) → (Fin n → μ.support) := fun h j => ⟨(h (Fin.rev j) : G)⁻¹, hmem _⟩
  have hr : ∀ h, r (r h) = h := by
    intro h; funext j; apply Subtype.ext
    show ((h (Fin.rev (Fin.rev j)) : G)⁻¹)⁻¹ = h j
    rw [inv_inv, Fin.rev_rev]
  let e : (Fin n → μ.support) ≃ (Fin n → μ.support) := ⟨r, r, hr, hr⟩
  have hwt : ∀ q : Fin n → G, wt μ (revStep q) = wt μ q := by
    intro q
    unfold wt revStep
    rw [Finset.prod_congr rfl (fun i _ => hsymm (q (Fin.rev i)))]
    exact Equiv.prod_comp Fin.revPerm (fun i => μ (q i))
  unfold E
  conv_rhs => rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun h _ => ?_
  have : (fun i => ((e h i : μ.support) : G)) = revStep (fun i => (h i : G)) := rfl
  rw [this, hwt]

end Exp

/-! ## The chain induced on `X`, path by path -/

section Chain

variable [DecidableEq X] (μ : G →₀ ℝ) (x₀ : X)

/-- The walk `walkPos h m • x₀` avoids `x₀` at the times `1, …, N`. -/
def Avoid {n : ℕ} (N : ℕ) (h : Fin n → G) : Prop :=
  ∀ m, 1 ≤ m → m ≤ N → walkPos h m • x₀ ≠ x₀

/-- Path form of `avoidProb`: avoid `x₀` at times `1..N`, be at `y` at time `N`. -/
noncomputable def A (N : ℕ) (y : X) : ℝ := open Classical in
  E μ N (fun h => if Avoid x₀ N h ∧ walkPos h N • x₀ = y then 1 else 0)

/-- Avoid `x₀` at times `1..N`, be at `y` at time `N + 1`. -/
noncomputable def B (N : ℕ) (y : X) : ℝ := open Classical in
  E μ (N + 1) (fun h => if Avoid x₀ N h ∧ walkPos h (N + 1) • x₀ = y then 1 else 0)

/-- `P(T > N)`: no return to `x₀` at times `1..N`. -/
noncomputable def Q (N : ℕ) : ℝ := open Classical in
  E μ N (fun h => if Avoid x₀ N h then 1 else 0)

variable {μ x₀}

lemma walkKernel_eq (x y : X) :
    walkKernel (μ : G → ℝ) x y = ∑ g : μ.support, if (g : G) • x = y then μ g else 0 := by
  classical
  unfold walkKernel
  rw [tsum_eq_sum (s := μ.support)]
  · rw [← Finset.sum_coe_sort μ.support]
    refine Finset.sum_congr rfl fun g _ => ?_
    split_ifs <;> rfl
  · intro g hg
    split_ifs
    · exact Finsupp.notMem_support_iff.1 hg
    · rfl

lemma avoid_snoc {N : ℕ} (h : Fin N → G) (g : G) :
    Avoid x₀ N (Fin.snoc h g : Fin (N + 1) → G) ↔ Avoid x₀ N h := by
  unfold Avoid
  refine forall_congr' fun m => imp_congr_right fun _ => imp_congr_right fun hm => ?_
  rw [walkPos_init _ hm, Fin.init_snoc]

lemma avoid_init {N : ℕ} (h : Fin (N + 1) → G) :
    Avoid x₀ N h ↔ Avoid x₀ N (Fin.init h) := by
  conv_lhs => rw [← Fin.snoc_init_self h]
  exact avoid_snoc _ _

lemma walkPos_snoc_last {N : ℕ} (h : Fin N → G) (g : G) :
    walkPos (Fin.snoc h g : Fin (N + 1) → G) (N + 1) = g * walkPos h N := by
  rw [walkPos_last, Fin.init_snoc, Fin.snoc_last]

lemma avoid_succ {n : ℕ} (N : ℕ) (h : Fin n → G) :
    Avoid x₀ (N + 1) h ↔ Avoid x₀ N h ∧ walkPos h (N + 1) • x₀ ≠ x₀ := by
  unfold Avoid
  constructor
  · intro H
    exact ⟨fun m h1 h2 => H m h1 (by omega), H (N + 1) (by omega) le_rfl⟩
  · rintro ⟨H, H'⟩ m h1 h2
    rcases Nat.lt_or_ge m (N + 1) with hm | hm
    · exact H m h1 (by omega)
    · obtain rfl : m = N + 1 := by omega
      exact H'

open Classical in
lemma B_snoc (N : ℕ) (y : X) : B μ x₀ N y = E μ N (fun h => if Avoid x₀ N h then
    ∑ g : μ.support, if (g : G) • (walkPos h N • x₀) = y then μ g else 0 else 0) := by
  classical
  unfold B
  rw [E_succ]
  refine E_congr fun h => ?_
  by_cases hA : Avoid x₀ N h
  · rw [if_pos hA]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [walkPos_snoc_last, mul_smul]
    by_cases hy : (g : G) • walkPos h N • x₀ = y
    · rw [if_pos ⟨(avoid_snoc h g).2 hA, hy⟩, if_pos hy, mul_one]
    · rw [if_neg (fun H => hy H.2), if_neg hy, mul_zero]
  · rw [if_neg hA]
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [if_neg (fun H => hA ((avoid_snoc h g).1 H.1)), mul_zero]

lemma kernel_sum (N : ℕ) (y : X) :
    ∑' z, A μ x₀ N z * walkKernel (μ : G → ℝ) z y = B μ x₀ N y := by
  classical
  rw [B_snoc]
  unfold A E
  simp_rw [Finset.sum_mul]
  have hsingle : ∀ h : Fin N → μ.support, ∀ z, z ≠ walkPos (fun i => (h i : G)) N • x₀ →
      wt μ (fun i => (h i : G)) * (if Avoid x₀ N (fun i => (h i : G)) ∧
        walkPos (fun i => (h i : G)) N • x₀ = z then 1 else 0) *
        walkKernel (μ : G → ℝ) z y = 0 := by
    intro h z hz
    rw [if_neg (fun H => hz H.2.symm), mul_zero, zero_mul]
  rw [Summable.tsum_finsetSum (fun h _ => (hasSum_single _ (hsingle h)).summable)]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [tsum_eq_single _ (hsingle h), walkKernel_eq]
  by_cases hA : Avoid x₀ N (fun i => (h i : G))
  · rw [if_pos ⟨hA, rfl⟩, if_pos hA, mul_one]
  · rw [if_neg (fun H => hA H.1), if_neg hA, mul_zero, zero_mul]

lemma A_zero (z : X) : A μ x₀ 0 z = if x₀ = z then 1 else 0 := by
  classical
  unfold A
  rw [E_zero]
  have hA : Avoid x₀ 0 (Fin.elim0 : Fin 0 → G) := fun m h1 h2 => by omega
  simp only [walkPos_zero, one_smul]
  by_cases hz : x₀ = z
  · rw [if_pos ⟨hA, hz⟩, if_pos hz]
  · rw [if_neg (fun H => hz H.2), if_neg hz]

lemma E_zero_fun {n : ℕ} : E μ n (fun _ => 0) = 0 := by
  simp [E]

lemma A_succ (N : ℕ) (y : X) : A μ x₀ (N + 1) y = if y = x₀ then 0 else B μ x₀ N y := by
  classical
  unfold A B
  by_cases hy : y = x₀
  · rw [if_pos hy]
    refine Eq.trans (E_congr fun h => ?_) E_zero_fun
    rw [if_neg]
    rintro ⟨H, H'⟩
    exact ((avoid_succ N h).1 H).2 (H'.trans hy)
  · rw [if_neg hy]
    refine E_congr fun h => ?_
    have : Avoid x₀ (N + 1) h ∧ walkPos h (N + 1) • x₀ = y ↔
        Avoid x₀ N h ∧ walkPos h (N + 1) • x₀ = y := by
      rw [avoid_succ]
      constructor
      · exact fun H => ⟨H.1.1, H.2⟩
      · exact fun H => ⟨⟨H.1, fun e => hy (H.2.symm.trans e)⟩, H.2⟩
    by_cases hc : Avoid x₀ N h ∧ walkPos h (N + 1) • x₀ = y
    · rw [if_pos (this.2 hc), if_pos hc]
    · rw [if_neg (fun H => hc (this.1 H)), if_neg hc]

lemma B_zero (y : X) : B μ x₀ 0 y = walkKernel (μ : G → ℝ) x₀ y := by
  classical
  rw [← kernel_sum]
  simp_rw [A_zero]
  rw [tsum_eq_single x₀]
  · simp
  · intro b hb
    rw [if_neg (Ne.symm hb), zero_mul]

lemma avoidProb_eq (N : ℕ) (y : X) :
    avoidProb (walkKernel (μ : G → ℝ)) x₀ (N + 1) y = A μ x₀ (N + 1) y := by
  classical
  induction N generalizing y with
  | zero =>
    rw [A_succ, B_zero]
    simp only [avoidProb]
    split_ifs <;> rfl
  | succ N ih =>
    rw [A_succ, ← kernel_sum]
    simp only [avoidProb]
    simp_rw [← ih]
    split_ifs <;> rfl

lemma firstReturnProb_eq (N : ℕ) :
    firstReturnProb (walkKernel (μ : G → ℝ)) x₀ N = B μ x₀ N x₀ := by
  cases N with
  | zero => rw [B_zero]; rfl
  | succ N =>
    rw [← kernel_sum]
    simp only [firstReturnProb]
    simp_rw [avoidProb_eq]

lemma Q_zero : Q μ x₀ 0 = 1 := by
  classical
  unfold Q
  rw [E_zero, if_pos (show Avoid x₀ 0 (Fin.elim0 : Fin 0 → G) from fun m h1 h2 => by omega)]

lemma Q_succ (hμ : ThompsonAmenability.IsProbability μ) (N : ℕ) :
    Q μ x₀ (N + 1) = Q μ x₀ N - B μ x₀ N x₀ := by
  classical
  have h1 : Q μ x₀ N = E μ (N + 1) (fun h => if Avoid x₀ N h then 1 else 0) := by
    unfold Q
    rw [← E_init hμ]
    refine E_congr fun h => ?_
    by_cases hA : Avoid x₀ N h
    · rw [if_pos hA, if_pos ((avoid_init h).1 hA)]
    · rw [if_neg hA, if_neg (fun H => hA ((avoid_init h).2 H))]
  rw [h1]
  unfold Q B
  rw [← E_sub]
  refine E_congr fun h => ?_
  by_cases hA : Avoid x₀ N h
  · by_cases he : walkPos h (N + 1) • x₀ = x₀
    · rw [if_neg (fun H => ((avoid_succ N h).1 H).2 he), if_pos hA, if_pos ⟨hA, he⟩]; ring
    · rw [if_pos ((avoid_succ N h).2 ⟨hA, he⟩), if_pos hA, if_neg (fun H => he H.2)]; ring
  · rw [if_neg (fun H => hA ((avoid_succ N h).1 H).1), if_neg hA, if_neg (fun H => hA H.1)]
    ring

lemma Q_eq (hμ : ThompsonAmenability.IsProbability μ) (N : ℕ) :
    Q μ x₀ N = 1 - ∑ j ∈ Finset.range N, firstReturnProb (walkKernel (μ : G → ℝ)) x₀ j := by
  induction N with
  | zero => simp [Q_zero]
  | succ N ih =>
    rw [Q_succ hμ, ih, Finset.sum_range_succ, firstReturnProb_eq]
    ring

end Chain

/-! ## Inverted orbits: `E|O_{n+1}| - E|O_n| = P(T > n + 1)` -/

section Orbit

variable [DecidableEq X] {μ : G →₀ ℝ} {x₀ : X}

lemma invertedOrbit_succ {n : ℕ} (h : Fin (n + 1) → G) :
    invertedOrbit x₀ h =
      insert ((walkPos h (n + 1))⁻¹ • x₀) (invertedOrbit x₀ (Fin.init h)) := by
  unfold invertedOrbit
  rw [Finset.range_add_one, Finset.image_insert]
  congr 1
  refine Finset.image_congr fun k hk => ?_
  have hk' : k < n + 1 := by simpa using hk
  rw [walkPos_init h (by omega)]

lemma mem_invertedOrbit_init_iff {n : ℕ} (h : Fin (n + 1) → G) :
    (walkPos h (n + 1))⁻¹ • x₀ ∈ invertedOrbit x₀ (Fin.init h) ↔
      ¬ Avoid x₀ (n + 1) (revStep h) := by
  have key : ∀ k, k ≤ n → ((walkPos (Fin.init h) k)⁻¹ • x₀ = (walkPos h (n + 1))⁻¹ • x₀ ↔
      walkPos (revStep h) (n + 1 - k) • x₀ = x₀) := by
    intro k hk
    rw [← walkPos_init h hk, ← walkPos_mul_inv h (by omega : k ≤ n + 1), mul_smul,
      inv_smul_eq_iff, eq_comm]
  unfold invertedOrbit Avoid
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, e⟩ H
    exact H (n + 1 - k) (by omega) (by omega) ((key k (by omega)).1 e)
  · intro H
    simp only [not_forall, not_not] at H
    obtain ⟨m, h1, h2, e⟩ := H
    refine ⟨n + 1 - m, by omega, (key (n + 1 - m) (by omega)).2 ?_⟩
    rwa [show n + 1 - (n + 1 - m) = m by omega]

open Classical in
lemma card_succ {n : ℕ} (h : Fin (n + 1) → G) :
    ((invertedOrbit x₀ h).card : ℝ) = (invertedOrbit x₀ (Fin.init h)).card +
      if Avoid x₀ (n + 1) (revStep h) then 1 else 0 := by
  rw [invertedOrbit_succ, Finset.card_insert_eq_ite]
  by_cases hm : (walkPos h (n + 1))⁻¹ • x₀ ∈ invertedOrbit x₀ (Fin.init h)
  · rw [if_pos hm, if_neg ((mem_invertedOrbit_init_iff h).1 hm), add_zero]
  · rw [if_neg hm, if_pos (not_not.1 (fun H => hm ((mem_invertedOrbit_init_iff h).2 H)))]
    push_cast; ring

variable (μ x₀)

/-- `E|O_n|`. -/
noncomputable def Card (n : ℕ) : ℝ := E μ n (fun h => ((invertedOrbit x₀ h).card : ℝ))

variable {μ x₀}

lemma Card_zero : Card μ x₀ 0 = 1 := by
  unfold Card
  rw [E_zero]
  simp [invertedOrbit, walkPos_zero]

lemma Card_succ (hμ : ThompsonAmenability.IsProbability μ) (hsymm : IsSymmetric μ) (n : ℕ) :
    Card μ x₀ (n + 1) = Card μ x₀ n + Q μ x₀ (n + 1) := by
  classical
  unfold Card
  rw [E_congr card_succ, E_add,
    E_init hμ n (fun h => ((invertedOrbit x₀ h).card : ℝ))]
  congr 1
  unfold Q
  exact E_rev hsymm (n + 1) (fun h => if Avoid x₀ (n + 1) h then 1 else 0)

lemma Card_eq (hμ : ThompsonAmenability.IsProbability μ) (hsymm : IsSymmetric μ) (n : ℕ) :
    Card μ x₀ n = ∑ j ∈ Finset.range (n + 1), Q μ x₀ j := by
  induction n with
  | zero => simp [Card_zero, Q_zero]
  | succ n ih => rw [Card_succ hμ hsymm, ih, Finset.sum_range_succ _ (n + 1)]

end Orbit

/-! ## The limit -/

section Limit

variable [DecidableEq X] {μ : G →₀ ℝ} {x₀ : X}

lemma firstReturnProb_nonneg (hμ : ThompsonAmenability.IsProbability μ) (j : ℕ) :
    0 ≤ firstReturnProb (walkKernel (μ : G → ℝ)) x₀ j := by
  classical
  rw [firstReturnProb_eq]
  exact E_nonneg hμ.1 fun h => by split_ifs <;> norm_num

lemma Q_nonneg (hμ : ThompsonAmenability.IsProbability μ) (j : ℕ) : 0 ≤ Q μ x₀ j := by
  classical
  exact E_nonneg hμ.1 fun h => by split_ifs <;> norm_num

/-- The paper's identity, in the limit: `(1/n) E|O_n| → P(T = ∞) = 1 - ∑ P(T = k)`. -/
theorem tendsto_main (hμ : ThompsonAmenability.IsProbability μ) (hsymm : IsSymmetric μ) :
    HasSum (firstReturnProb (walkKernel (μ : G → ℝ)) x₀)
        (∑' j, firstReturnProb (walkKernel (μ : G → ℝ)) x₀ j) ∧
      Filter.Tendsto
        (fun n : ℕ => (1 / (n : ℝ)) * walkExp μ n fun h => ((invertedOrbit x₀ h).card : ℝ))
        Filter.atTop (nhds (1 - ∑' j, firstReturnProb (walkKernel (μ : G → ℝ)) x₀ j)) := by
  set fr := firstReturnProb (walkKernel (μ : G → ℝ)) x₀ with hfr
  have hpart : ∀ N, ∑ j ∈ Finset.range N, fr j ≤ 1 := by
    intro N
    have := Q_nonneg (x₀ := x₀) hμ N
    rw [Q_eq hμ] at this
    linarith
  have hsum : Summable fr := summable_of_sum_range_le (firstReturnProb_nonneg hμ) hpart
  have hs := hsum.hasSum
  refine ⟨hs, ?_⟩
  have hQ : Filter.Tendsto (fun N => Q μ x₀ N) Filter.atTop (nhds (1 - ∑' j, fr j)) := by
    have : (fun N => Q μ x₀ N) = fun N => 1 - ∑ j ∈ Finset.range N, fr j := by
      funext N; rw [Q_eq hμ]
    rw [this]
    exact tendsto_const_nhds.sub hs.tendsto_sum_nat
  have hQle : ∀ N, Q μ x₀ N ≤ 1 := by
    intro N
    rw [Q_eq hμ]
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.range N) => firstReturnProb_nonneg (x₀ := x₀) hμ j
    linarith
  have h2 : Filter.Tendsto (fun n : ℕ => Q μ x₀ n / n) Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun n => div_nonneg (Q_nonneg hμ n) n.cast_nonneg) (fun n => ?_)
      (tendsto_const_div_atTop_nhds_zero_nat 1)
    exact div_le_div_of_nonneg_right (hQle n) n.cast_nonneg
  have h3 := hQ.cesaro.add h2
  rw [add_zero] at h3
  refine h3.congr fun n => ?_
  rw [walkExp_eq, ← Card, Card_eq hμ hsymm, Finset.sum_range_succ]
  ring

theorem isRecurrentChain_iff (hμ : ThompsonAmenability.IsProbability μ) (hsymm : IsSymmetric μ) :
    IsRecurrentChain (walkKernel (μ : G → ℝ)) x₀ ↔
      Filter.Tendsto
        (fun n : ℕ => (1 / (n : ℝ)) * walkExp μ n fun h => ((invertedOrbit x₀ h).card : ℝ))
        Filter.atTop (nhds 0) := by
  obtain ⟨hs, ht⟩ := tendsto_main (x₀ := x₀) hμ hsymm
  constructor
  · intro hr
    rw [hr.tsum_eq, sub_self] at ht
    exact ht
  · intro h0
    have := tendsto_nhds_unique ht h0
    have h1 : ∑' j, firstReturnProb (walkKernel (μ : G → ℝ)) x₀ j = 1 := by linarith
    unfold IsRecurrentChain
    rwa [h1] at hs

end Limit

/-! ## The comparison step (proved in `JMMS.IETRC` above)

`IsRecurrentAction` asks for recurrence for *every* symmetric finitely supported probability `ν`
and *every* base point, while the inverted-orbit identity above concerns the single measure `μ`
and the single base point `x₀`. Passing from one to the other is the standard fact that, for a
transitive action and a symmetric finitely supported generating `μ`, recurrence of the induced
chain does not depend on the base point nor on the symmetric finitely supported measure (each
`s ∈ supp ν` is a word of bounded length in `supp μ`, so the Dirichlet forms satisfy
`D_ν ≤ C · D_μ`; recurrence is vanishing capacity by the Dirichlet principle). This is a real
theorem of electrical-network theory that the paper uses without comment; it is isolated here. -/
theorem isRecurrentChain_comparison {G X : Type*} [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X] (μ : G →₀ ℝ) (hμ : ThompsonAmenability.IsProbability μ)
    (hsymm : IsSymmetric μ) (hnd : IsNondegenerate μ) (x₀ : X)
    (hrec : IsRecurrentChain (walkKernel (μ : G → ℝ)) x₀)
    (ν : G →₀ ℝ) (hν : ThompsonAmenability.IsProbability ν) (hνsymm : IsSymmetric ν) (y : X) :
    IsRecurrentChain (walkKernel (ν : G → ℝ)) y :=
  JMMS.IETRC.isRecurrentChain_comparison μ hμ hsymm hnd x₀ hrec ν hν hνsymm y

end JMMS.IETP43

namespace JMMS

theorem chk_isRecurrentAction_iff_tendsto_card_invertedOrbit_div {G X : Type*} [Group G]
    [MulAction G X] [DecidableEq X] [Group.FG G] [MulAction.IsPretransitive G X] (μ : G →₀ ℝ)
    (hμ : ThompsonAmenability.IsProbability μ) (hsymm : IsSymmetric μ) (hnd : IsNondegenerate μ)
    (x₀ : X) :
    IsRecurrentAction G X ↔
      Filter.Tendsto
        (fun n : ℕ => (1 / (n : ℝ)) * walkExp μ n fun h => ((invertedOrbit x₀ h).card : ℝ))
        Filter.atTop (nhds 0) := by
  rw [← IETP43.isRecurrentChain_iff hμ hsymm]
  constructor
  · intro H
    exact H μ hμ hsymm x₀
  · intro H ν hν hνsymm y
    exact IETP43.isRecurrentChain_comparison μ hμ hsymm hnd x₀ H ν hν hνsymm y

end JMMS

end

open IntervalExchange
open JMMS in
theorem solution {G X : Type*} [Group G]
    [MulAction G X] [DecidableEq X] [Group.FG G] [MulAction.IsPretransitive G X] (μ : G →₀ ℝ)
    (hμ : ThompsonAmenability.IsProbability μ) (hsymm : IsSymmetric μ) (hnd : IsNondegenerate μ)
    (x₀ : X) :
    IsRecurrentAction G X ↔
      Filter.Tendsto
        (fun n : ℕ => (1 / (n : ℝ)) * walkExp μ n fun h => ((invertedOrbit x₀ h).card : ℝ))
        Filter.atTop (nhds 0) :=
  JMMS.chk_isRecurrentAction_iff_tendsto_card_invertedOrbit_div μ hμ hsymm hnd x₀
