-- Prove2me | solution 1 for JMMS.isLiouville_of_rationalRank_eq_one_and_hasNontrivialBoundary_of_three_le_rationalRank
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T18:23:18.672879+00:00
-- url     : https://prove2.me/submissions/623abcf7-fa21-41c8-b9fc-be7f77109461

import Mathlib
import Definitions.Def_IntervalExchange
import Theorems.Thm_MarkovMixing_polya_recurrence
import Theorems.Thm_JMMS_mem_IET_iff
import Definitions.Def_CantorSystems
import Definitions.Def_ErschlerZheng_Walks
import Theorems.Thm_JMMS_exists_isMinimal_subshift_mulEquiv_IETOn_and_complexity_le
import Theorems.Thm_JMMS_entropy_convPow_le_and_asymptoticEntropy_eq_zero_of_virtuallyCyclic
import Theorems.Thm_KaimanovichVershik_not_hasNontrivialPoissonBoundary_iff_asymptoticEntropy_eq_zero

section

/-!
# JMMS Theorem 1.10 (= Theorem 5.4)

Juschenko, Matte Bon, Monod and de la Salle, *Extensive amenability and an application to interval
exchanges*, arXiv:1503.04977.

(i) Rational rank 1: the realization of `IET(Λ; Σ)` as the topological full group of a minimal
Cantor subshift (Proposition 5.11 + Lemma 5.13), divided by the kernel of the shift action so that
the action is free, Matte Bon's entropy theorem for virtually cyclic groups, and the
Kaimanovich–Vershik entropy criterion.

(ii) Rational rank ≥ 3: transience of the orbit walk by comparison with `ℤ³` (Pólya) through
Dirichlet forms (no symmetry of `μ` needed), stabilisation of the cocycle `τ_{g_n}(x)` at each
point, bounded harmonic functions from its limit law, a 0–1 law (point masses), and the paper's
Lemma 5.7 argument.
-/

/-! # Theorem 1.10, part A: generic Markov-chain and Dirichlet-form machinery
(adapted from the proved solutions of JMMS's comparison lemma and Lemma 5.2). -/

open IntervalExchange

set_option linter.unusedSectionVars false

namespace JMMS.IETT110

open Classical

section Group

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

end Group

/-! ## Part 1: generic Markov-chain bookkeeping -/

section Markov

variable {V : Type*} (P : V → V → ℝ) (x : V)

/-- The (sub-probability) of being at `y` at time `t` without having visited `x` at times
`1, …, t`, the chain being at `x` at time `0`. -/
noncomputable def av : ℕ → V → ℝ
  | 0, y => if y = x then 1 else 0
  | t + 1, y => if y = x then 0 else ∑' z, av t z * P z y

variable {P}

lemma hasSum_of_fiber {α β : Type*} (K : α × β → ℝ) (hK : 0 ≤ K) (s : α → ℝ)
    (hs : ∀ a, HasSum (fun b => K (a, b)) (s a)) (hsum : Summable s) (g : β → ℝ)
    (hg : ∀ b, HasSum (fun a => K (a, b)) (g b)) : HasSum g (∑' a, s a) := by
  have hKs : Summable K := by
    rw [summable_prod_of_nonneg hK]
    refine ⟨fun a => (hs a).summable, ?_⟩
    simpa [(hs _).tsum_eq] using hsum
  have h1 : HasSum K (∑' a, s a) := by
    have := hKs.hasSum
    rwa [hKs.tsum_prod' (fun a => (hs a).summable), tsum_congr fun a => (hs a).tsum_eq] at this
  have h2 : HasSum (K ∘ (Equiv.prodComm β α)) (∑' a, s a) :=
    (Equiv.hasSum_iff (Equiv.prodComm β α)).mpr h1
  exact h2.prod_fiberwise fun b => hg b

variable (hP0 : ∀ a b, 0 ≤ P a b) (hP1 : ∀ a, HasSum (P a) 1)
include hP0

lemma av_nonneg : ∀ t y, 0 ≤ av P x t y
  | 0, y => by simp only [av]; split_ifs <;> norm_num
  | t + 1, y => by
    simp only [av]
    split_ifs
    · exact le_rfl
    · exact tsum_nonneg fun z => mul_nonneg (av_nonneg t z) (hP0 z y)

include hP1

lemma P_le_one (a b : V) : P a b ≤ 1 :=
  le_hasSum (hP1 a) b fun c _ => hP0 a c

lemma summable_F (t : ℕ) (ih : Summable (av P x t)) :
    Summable (fun p : V × V => av P x t p.1 * P p.1 p.2) := by
  have hK : 0 ≤ (fun p : V × V => av P x t p.1 * P p.1 p.2) := by
    intro p
    exact mul_nonneg (av_nonneg x hP0 t p.1) (hP0 _ _)
  refine (summable_prod_of_nonneg hK).mpr ⟨fun a => ?_, ?_⟩
  · exact (hP1 a).summable.mul_left (av P x t a)
  refine ih.congr fun a => ?_
  show av P x t a = ∑' y, av P x t a * P a y
  rw [tsum_mul_left, (hP1 a).tsum_eq, mul_one]

/-- Summability of `av t` and the identity `∑ (av (t+1)) + f_t = ∑ (av t)`. -/
lemma av_summable : ∀ t, Summable (av P x t)
  | 0 => by
    refine summable_of_ne_finset_zero (s := {x}) fun y hy => ?_
    simp only [Finset.mem_singleton] at hy
    simp [av, hy]
  | t + 1 => by
    have ih := av_summable t
    have hF := summable_F x hP0 hP1 t ih
    have hG : Summable (fun y => ∑' z, av P x t z * P z y) := hF.prod_symm.prod
    refine Summable.of_nonneg_of_le (fun y => av_nonneg x hP0 (t + 1) y) (fun y => ?_) hG
    simp only [av]
    split_ifs
    · exact tsum_nonneg fun z => mul_nonneg (av_nonneg x hP0 t z) (hP0 z y)
    · exact le_rfl

lemma av_step (t : ℕ) :
    ∑' y, av P x (t + 1) y + ∑' z, av P x t z * P z x = ∑' y, av P x t y := by
  have ih := av_summable x hP0 hP1 t
  have hF := summable_F x hP0 hP1 t ih
  have hG : Summable (fun y => ∑' z, av P x t z * P z y) := hF.prod_symm.prod
  have e1 := hG.tsum_eq_add_tsum_ite x
  have e2 : ∑' y, av P x (t + 1) y = ∑' y, if y = x then 0 else ∑' z, av P x t z * P z y :=
    tsum_congr fun y => rfl
  rw [e2, add_comm, ← e1]
  rw [Summable.tsum_comm' (f := fun z y => av P x t z * P z y) hF
    (fun z => (hP1 z).summable.mul_left (av P x t z))
    (fun y => (hF.prod_symm.prod_factor y))]
  exact tsum_congr fun z => by rw [tsum_mul_left, (hP1 z).tsum_eq, mul_one]

omit hP0 hP1 in
lemma avoidProb_eq_av : ∀ k y, avoidProb P x (k + 1) y = av P x (k + 1) y
  | 0, y => by
    simp only [avoidProb, av]
    split_ifs with h
    · rfl
    · rw [tsum_eq_single x]
      · simp
      · intro z hz; simp [hz]
  | k + 1, y => by
    simp only [avoidProb]
    rw [show av P x (k + 2) y = if y = x then 0 else ∑' z, av P x (k + 1) z * P z y from rfl]
    split_ifs
    · rfl
    · exact tsum_congr fun z => by rw [avoidProb_eq_av k z]

omit hP0 hP1 in
lemma firstReturnProb_eq_av (t : ℕ) : firstReturnProb P x t = ∑' z, av P x t z * P z x := by
  cases t with
  | zero =>
    simp only [firstReturnProb, av]
    rw [tsum_eq_single x]
    · simp
    · intro z hz; simp [hz]
  | succ k =>
    simp only [firstReturnProb]
    exact tsum_congr fun z => by rw [avoidProb_eq_av x k z]

lemma partial_sum (t : ℕ) :
    ∑ n ∈ Finset.range t, firstReturnProb P x n = 1 - ∑' y, av P x t y := by
  induction t with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, av]
    rw [tsum_eq_single x]
    · simp
    · intro z hz; simp [hz]
  | succ t ih =>
    rw [Finset.sum_range_succ, ih, firstReturnProb_eq_av x, ← av_step x hP0 hP1 t]
    ring

/-- The path-sum description of `av`. -/
lemma path_hasSum : ∀ (t : ℕ) (y : V),
    HasSum (fun ω : Fin (t + 1) → V =>
      if (ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → ω i ∉ ({x} : Set V)) ∧ ω (Fin.last t) = y
      then MarkovMixing.pathWeightC P ω else 0) (av P x t y)
  | 0, y => by
    by_cases hy : y = x
    · subst hy
      have : (fun ω : Fin 1 → V =>
          if (ω 0 = y ∧ ∀ i : Fin 1, i ≠ 0 → ω i ∉ ({y} : Set V)) ∧ ω (Fin.last 0) = y
          then MarkovMixing.pathWeightC P ω else 0) = fun ω => if ω = fun _ => y then 1 else 0 := by
        funext ω
        have hw : MarkovMixing.pathWeightC P ω = 1 := by simp [MarkovMixing.pathWeightC]
        have e : (ω = fun _ => y) ↔ ω 0 = y := by
          constructor
          · intro h; rw [h]
          · intro h; funext i; rw [Subsingleton.elim i 0, h]
        rw [hw]
        have : Fin.last 0 = 0 := rfl
        simp only [this]
        by_cases h : ω 0 = y
        · have h' : ω = fun _ => y := e.mpr h
          rw [if_pos h', if_pos]
          refine ⟨⟨h, fun i hi => absurd (Subsingleton.elim i 0) hi⟩, h⟩
        · have h' : ¬ ω = fun _ => y := fun h' => h (e.mp h')
          rw [if_neg h', if_neg]
          exact fun hh => h hh.2
      rw [this]
      have : av P y 0 y = 1 := by simp [av]
      rw [this]
      exact hasSum_ite_eq _ _
    · have : av P x 0 y = 0 := by simp [av, hy]
      rw [this]
      convert hasSum_zero with ω
      split_ifs with h
      · exact absurd (h.2.symm.trans (show ω (Fin.last 0) = x from h.1.1)) hy
      · rfl
  | t + 1, y => by
    by_cases hy : y = x
    · subst hy
      have : av P y (t + 1) y = 0 := by simp [av]
      rw [this]
      convert hasSum_zero with ω
      split_ifs with h
      · exact absurd h.2 (h.1.2 _ (Fin.last_pos.ne'))
      · rfl
    have ih := path_hasSum t
    -- the paths of length `t`, weighted by the last step to `y`
    let g : (Fin (t + 1) → V) → ℝ := fun ω' =>
      (if ω' 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → ω' i ∉ ({x} : Set V)
        then MarkovMixing.pathWeightC P ω' else 0) * P (ω' (Fin.last t)) y
    have hg : HasSum g (∑' z, av P x t z * P z y) := by
      refine hasSum_of_fiber (fun p : V × (Fin (t + 1) → V) =>
          (if (p.2 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → p.2 i ∉ ({x} : Set V)) ∧
            p.2 (Fin.last t) = p.1 then MarkovMixing.pathWeightC P p.2 else 0) * P p.1 y)
        ?_ (fun z => av P x t z * P z y) (fun z => (ih z).mul_right _) ?_ g ?_
      · intro p
        refine mul_nonneg ?_ (hP0 _ _)
        dsimp only
        split_ifs
        · exact Finset.prod_nonneg fun i _ => hP0 _ _
        · exact le_rfl
      · refine Summable.of_nonneg_of_le (fun z => mul_nonneg (av_nonneg x hP0 t z) (hP0 z y))
          (fun z => ?_) (av_summable x hP0 hP1 t)
        exact mul_le_of_le_one_right (av_nonneg x hP0 t z) (P_le_one hP0 hP1 z y)
      · intro ω'
        convert hasSum_ite_eq (ω' (Fin.last t)) (g ω') using 1
        funext z
        dsimp only [g]
        by_cases hz : z = ω' (Fin.last t)
        · subst hz; simp
        · simp [hz, Ne.symm hz]
    have key : ∀ (y' : V) (ω' : Fin (t + 1) → V),
        (if ((Fin.snoc (α := fun _ => V) ω' y') 0 = x ∧ ∀ i : Fin (t + 2), i ≠ 0 →
            (Fin.snoc (α := fun _ => V) ω' y') i ∉ ({x} : Set V)) ∧
            (Fin.snoc (α := fun _ => V) ω' y') (Fin.last (t + 1)) = y
          then MarkovMixing.pathWeightC P (Fin.snoc (α := fun _ => V) ω' y') else 0) =
          if y' = y then g ω' else 0 := by
      intro y' ω'
      have hw : MarkovMixing.pathWeightC P (Fin.snoc (α := fun _ => V) ω' y') =
          MarkovMixing.pathWeightC P ω' * P (ω' (Fin.last t)) y' := by
        simp only [MarkovMixing.pathWeightC]
        rw [Fin.prod_univ_castSucc]
        congr 1
        · refine Finset.prod_congr rfl fun i _ => ?_
          rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
        · rw [Fin.succ_last, Fin.snoc_castSucc, Fin.snoc_last]
      have h0 : (Fin.snoc (α := fun _ => V) ω' y') 0 = ω' 0 := by
        rw [show (0 : Fin (t + 2)) = Fin.castSucc 0 from rfl, Fin.snoc_castSucc]
      have hall : (∀ i : Fin (t + 2), i ≠ 0 → (Fin.snoc (α := fun _ => V) ω' y') i ∉ ({x} : Set V))
          ↔ (∀ i : Fin (t + 1), i ≠ 0 → ω' i ∉ ({x} : Set V)) ∧ y' ≠ x := by
        rw [Fin.forall_fin_succ']
        simp [Fin.snoc_castSucc, Fin.snoc_last]
      rw [hw, h0, Fin.snoc_last]
      by_cases hy' : y' = y
      · subst hy'
        simp only [g, if_true]
        by_cases hc : ω' 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → ω' i ∉ ({x} : Set V)
        · rw [if_pos ⟨⟨hc.1, hall.mpr ⟨hc.2, hy⟩⟩, by simp⟩, if_pos hc]
        · rw [if_neg, if_neg hc, zero_mul]
          exact fun h => hc ⟨h.1.1, (hall.mp h.1.2).1⟩
      · rw [if_neg hy', if_neg]
        exact fun h => hy' h.2
    let e := Fin.snocEquiv (fun _ : Fin (t + 2) => V)
    rw [← e.hasSum_iff]
    have hinj : Function.Injective (fun ω' : Fin (t + 1) → V => (y, ω')) :=
      fun a b h => (Prod.ext_iff.mp h).2
    rw [← hinj.hasSum_iff]
    · convert hg using 1
      · funext ω'
        exact (key y ω').trans (if_pos rfl)
      · simp [av, hy]
    · rintro ⟨y', ω'⟩ hp
      have hy' : y' ≠ y := fun h => hp ⟨ω', by simp [h]⟩
      exact (key y' ω').trans (if_neg hy')

lemma returnTailC_eq [Countable V] [DecidableEq V] (t : ℕ) :
    MarkovMixing.returnTailC P x t = ∑' y, av P x t y := by
  let g : (Fin (t + 1) → V) → ℝ := fun ω =>
    if ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → ω i ∉ ({x} : Set V)
    then MarkovMixing.pathWeightC P ω else 0
  have hg : HasSum g (∑' y, av P x t y) := by
    refine hasSum_of_fiber (fun p : V × (Fin (t + 1) → V) =>
        if (p.2 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → p.2 i ∉ ({x} : Set V)) ∧
          p.2 (Fin.last t) = p.1 then MarkovMixing.pathWeightC P p.2 else 0)
      ?_ (av P x t) (fun y => by convert path_hasSum x hP0 hP1 t y) (av_summable x hP0 hP1 t) g ?_
    · intro p
      dsimp only
      split_ifs
      · exact Finset.prod_nonneg fun i _ => hP0 _ _
      · exact le_rfl
    · intro ω
      convert hasSum_ite_eq (ω (Fin.last t)) (g ω) using 1
      funext z
      dsimp only [g]
      by_cases hz : z = ω (Fin.last t)
      · subst hz; simp
      · simp [hz, Ne.symm hz]
  unfold MarkovMixing.returnTailC MarkovMixing.setAvoidTailC
  rw [← hg.tsum_eq]
  exact tsum_congr fun ω => by simp only [g]; congr

end Markov

section Bridge

variable {V : Type*} {P : V → V → ℝ} (x : V)

lemma recurrent_of_isRecurrentChain [Countable V] [DecidableEq V]
    (hP0 : ∀ a b, 0 ≤ P a b) (hP1 : ∀ a, HasSum (P a) 1) (h : IsRecurrentChain P x) : MarkovMixing.Recurrent P x := by
  unfold MarkovMixing.Recurrent
  have h1 := h.tendsto_sum_nat
  have h2 : Filter.Tendsto (fun t => 1 - ∑ n ∈ Finset.range t, firstReturnProb P x n)
      Filter.atTop (nhds (1 - 1)) := tendsto_const_nhds.sub h1
  rw [sub_self] at h2
  refine h2.congr fun t => ?_
  rw [partial_sum x hP0 hP1, returnTailC_eq x hP0 hP1]
  ring

end Bridge

end JMMS.IETT110

/-! # Theorem 1.10, part B: a Hardy inequality on `ℤ³` from Pólya's theorem -/

open IntervalExchange

set_option linter.unusedSectionVars false

namespace JMMS.IETT110

open Classical

section WalkKernel

variable {G X : Type*} [Group G] [MulAction G X] (μ : G →₀ ℝ)

lemma wk_eq (x y : X) :
    walkKernel (μ : G → ℝ) x y = ∑ g ∈ μ.support, if g • x = y then μ g else 0 := by
  unfold walkKernel
  rw [tsum_eq_sum]
  intro g hg
  rw [Finsupp.notMem_support_iff.mp hg]
  simp

variable {μ}

lemma wk_nonneg (hμ : ThompsonAmenability.IsProbability μ) (x y : X) :
    0 ≤ walkKernel (μ : G → ℝ) x y := by
  rw [wk_eq]
  exact Finset.sum_nonneg fun g _ => by split_ifs; exacts [hμ.1 g, le_rfl]

lemma wk_hasSum (hμ : ThompsonAmenability.IsProbability μ) (x : X) :
    HasSum (walkKernel (μ : G → ℝ) x) 1 := by
  have : walkKernel (μ : G → ℝ) x = fun y => ∑ g ∈ μ.support, if g • x = y then μ g else 0 :=
    funext (wk_eq μ x)
  rw [this, ← mass_one hμ]
  refine hasSum_sum fun g _ => ?_
  convert hasSum_ite_eq (g • x) (μ g) using 1
  funext y
  simp only [eq_comm]

end WalkKernel

/-! ## The simple random walk on `ℤ³` as a walk of translations -/

abbrev X3 := Fin 3 → ℤ

/-- The six unit vectors `±eᵢ`. -/
def S6 : Finset X3 :=
  Finset.univ.image fun p : Fin 3 × Bool => Pi.single p.1 (if p.2 then (1 : ℤ) else -1)

lemma card_S6 : S6.card = 6 := by decide

lemma mem_S6_iff (d : X3) :
    d ∈ S6 ↔ ∃ j : Fin 3, (∀ i, i ≠ j → d i = 0) ∧ (d j = 1 ∨ d j = -1) := by
  constructor
  · intro hd
    obtain ⟨⟨j, b⟩, -, rfl⟩ := Finset.mem_image.1 hd
    refine ⟨j, fun i hi => by simp [hi], ?_⟩
    cases b <;> simp
  · rintro ⟨j, h0, h1⟩
    refine Finset.mem_image.2 ⟨(j, decide (d j = 1)), Finset.mem_univ _, ?_⟩
    funext i
    by_cases hi : i = j
    · subst hi
      rcases h1 with h | h <;> simp [h]
    · simp [hi, h0 i hi]

lemma neg_mem_S6 {d : X3} (hd : d ∈ S6) : -d ∈ S6 := by
  rw [mem_S6_iff] at *
  obtain ⟨j, h0, h1⟩ := hd
  refine ⟨j, fun i hi => by simp [h0 i hi], ?_⟩
  simp only [Pi.neg_apply]
  rcases h1 with h | h <;> simp [h]

/-- The uniform measure on the six unit translations. -/
noncomputable def μ3 : Equiv.Perm X3 →₀ ℝ :=
  ∑ v ∈ S6, Finsupp.single (Equiv.addRight v) (1 / 6 : ℝ)

lemma μ3_apply (g : Equiv.Perm X3) :
    μ3 g = ∑ v ∈ S6, if Equiv.addRight v = g then (1 / 6 : ℝ) else 0 := by
  unfold μ3
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finsupp.single_apply]

lemma μ3_nonneg (g : Equiv.Perm X3) : 0 ≤ μ3 g := by
  rw [μ3_apply]
  exact Finset.sum_nonneg fun v _ => by split_ifs <;> norm_num

lemma μ3_prob : ThompsonAmenability.IsProbability μ3 := by
  refine ⟨μ3_nonneg, ?_⟩
  unfold μ3
  rw [← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  simp only [Finsupp.sum_single_index, Finset.sum_const, card_S6]
  norm_num

lemma μ3_symm : IsSymmetric μ3 := by
  intro g
  rw [μ3_apply, μ3_apply]
  refine Finset.sum_nbij' (fun v => -v) (fun v => -v) (fun v hv => neg_mem_S6 hv)
    (fun v hv => neg_mem_S6 hv) (fun v _ => neg_neg v) (fun v _ => neg_neg v) ?_
  intro v _
  have : (Equiv.addRight (-v) = g) ↔ (Equiv.addRight v = g⁻¹) := by
    constructor
    · rintro rfl; ext x; simp
    · intro h; rw [← inv_inv g, ← h]; ext x; simp [sub_eq_add_neg]
  by_cases h : Equiv.addRight v = g⁻¹
  · rw [if_pos h, if_pos (this.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (this.1 h'))]

lemma walkKernel_μ3 : walkKernel (μ3 : Equiv.Perm X3 → ℝ) = MarkovMixing.srwZ 3 := by
  funext x y
  unfold walkKernel
  simp_rw [μ3_apply]
  have e : ∀ g : Equiv.Perm X3, (if g • x = y then
      ∑ v ∈ S6, (if Equiv.addRight v = g then (1 / 6 : ℝ) else 0) else 0) =
      ∑ v ∈ S6, if Equiv.addRight v = g then (if x + v = y then (1 / 6 : ℝ) else 0) else 0 := by
    intro g
    split_ifs with h
    · refine Finset.sum_congr rfl fun v _ => ?_
      split_ifs with h1 h2
      · rfl
      · exfalso; apply h2; subst h1; simpa using h
      · rfl
    · symm
      refine Finset.sum_eq_zero fun v _ => ?_
      split_ifs with h1 h2
      · exfalso; apply h; subst h1; simpa using h2
      · rfl
      · rfl
  simp_rw [e]
  rw [Summable.tsum_finsetSum (fun v _ => (hasSum_ite_eq (Equiv.addRight v)
    (if x + v = y then (1 / 6 : ℝ) else 0)).summable.congr fun g => by
      simp only [eq_comm])]
  have e2 : ∀ v : X3, ∑' g : Equiv.Perm X3, (if Equiv.addRight v = g then
      (if x + v = y then (1 / 6 : ℝ) else 0) else 0) = if x + v = y then (1 / 6 : ℝ) else 0 := by
    intro v
    rw [tsum_eq_single (Equiv.addRight v)]
    · simp
    · intro g hg; rw [if_neg (Ne.symm hg)]
  simp_rw [e2]
  -- at most one `v` with `x + v = y`
  unfold MarkovMixing.srwZ
  by_cases hd : y - x ∈ S6
  · rw [Finset.sum_eq_single (y - x)]
    · rw [if_pos (by abel), if_pos]
      · norm_num
      · exact (mem_S6_iff _).1 hd |>.imp fun j hj => ⟨fun i hi => by
          have := hj.1 i hi; simp only [Pi.sub_apply] at this; linarith,
          by rcases hj.2 with h | h <;> simp only [Pi.sub_apply] at h <;> [left; right] <;> linarith⟩
    · intro v _ hv
      rw [if_neg]
      intro h; apply hv; rw [← h]; abel
    · intro h; exact absurd hd h
  · rw [Finset.sum_eq_zero, if_neg]
    · rintro ⟨j, h0, h1⟩
      apply hd
      rw [mem_S6_iff]
      refine ⟨j, fun i hi => by simp [h0 i hi], ?_⟩
      simp only [Pi.sub_apply]
      rcases h1 with h | h <;> [left; right] <;> linarith
    · intro v hv
      rw [if_neg]
      intro h; apply hd; rw [← h]; simpa using hv

/-- The Hardy inequality at `0` for the simple random walk on `ℤ³`. -/
theorem hardy_Z3 : ∃ C, 0 ≤ C ∧ ∀ f : X3 → ℝ, FS f → f 0 ^ 2 ≤ C * B μ3 f f := by
  have hP0 := wk_nonneg (X := X3) μ3_prob
  have hP1 := wk_hasSum (X := X3) μ3_prob
  have hnr : ¬ IsRecurrentChain (walkKernel (μ3 : Equiv.Perm X3 → ℝ)) (0 : X3) := by
    intro h
    have := recurrent_of_isRecurrentChain (0 : X3) hP0 hP1 h
    rw [walkKernel_μ3] at this
    exact (MarkovMixing.polya_recurrence).2 3 le_rfl this
  unfold IsRecurrentChain at hnr
  have efr : firstReturnProb (walkKernel (μ3 : Equiv.Perm X3 → ℝ)) (0 : X3) = fr μ3 (0 : X3) :=
    funext fun n => firstReturnProb_eq n
  rw [efr] at hnr
  have hsν := fr_summable (o := (0 : X3)) μ3_prob
  have hle1 : ∑' k, fr μ3 (0 : X3) k ≤ 1 :=
    Real.tsum_le_of_sum_range_le (fr_nonneg μ3_prob.1) (fr_sum_le μ3_prob)
  have hlt : ∑' k, fr μ3 (0 : X3) k < 1 := by
    rcases hle1.lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ hsν.hasSum) hnr
  exact hardy_of_bdd μ3_prob μ3_symm (0 : X3) _ (u_bdd μ3_prob hlt)

end JMMS.IETT110

/-! # Theorem 1.10, part C: Hardy inequalities by comparison with `ℤ³`, and Green bounds

For a probability `μ` on `G` acting on `X`, the walk `z ↦ s⁻¹ • z` (`s ∼ μ`) has laws
`qlaw y n`, evolving by `R f z = ∑_s μ(s) f(s • z)`. Its truncated Green function
`U = ∑_{n<N} qlaw y n` satisfies `U - R U = δ_y - qlaw y N`, so `B_μ(U) ≤ 2 U(y)`; a Hardy
inequality at `y` and at `a` then bounds `U(a)`. -/

open IntervalExchange

set_option linter.unusedSectionVars false

namespace JMMS.IETT110

open Classical

section Green

variable {G X : Type*} [Group G] [MulAction G X]

/-- One step of the law of the walk `z ↦ s⁻¹ • z`. -/
noncomputable def R (μ : G →₀ ℝ) (f : X → ℝ) (z : X) : ℝ :=
  ∑ s ∈ μ.support, μ s * f (s • z)

lemma R_FS (μ : G →₀ ℝ) {f : X → ℝ} (hf : FS f) : FS (R μ f) := by
  have : FS (fun z => ∑ s ∈ μ.support, μ s * f (s • z)) :=
    FS.finset_sum _ fun s => (hf.comp_smul s).mul_left _
  exact this

lemma R_nonneg {μ : G →₀ ℝ} (hμ0 : ∀ g, 0 ≤ μ g) {f : X → ℝ} (hf : ∀ z, 0 ≤ f z) (z : X) :
    0 ≤ R μ f z :=
  Finset.sum_nonneg fun g _ => mul_nonneg (hμ0 g) (hf _)

lemma R_sum (μ : G →₀ ℝ) {ι : Type*} (s : Finset ι) (F : ι → X → ℝ) (z : X) :
    R μ (fun w => ∑ i ∈ s, F i w) z = ∑ i ∈ s, R μ (F i) z := by
  unfold R
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

/-- The law at time `n` of the walk `z ↦ s⁻¹ • z` started at `y`. -/
noncomputable def qlaw (μ : G →₀ ℝ) (y : X) : ℕ → X → ℝ
  | 0 => fun z => if z = y then 1 else 0
  | n + 1 => R μ (qlaw μ y n)

/-- The truncated Green function. -/
noncomputable def U (μ : G →₀ ℝ) (y : X) (N : ℕ) (z : X) : ℝ :=
  ∑ n ∈ Finset.range N, qlaw μ y n z

variable {μ : G →₀ ℝ}

lemma qlaw_FS (y : X) (n : ℕ) : FS (qlaw μ y n) := by
  induction n with
  | zero => exact FS.delta y
  | succ n ih => exact R_FS μ ih

lemma qlaw_nonneg (hμ0 : ∀ g, 0 ≤ μ g) (y : X) (n : ℕ) (z : X) : 0 ≤ qlaw μ y n z := by
  induction n generalizing z with
  | zero => simp only [qlaw]; split_ifs <;> norm_num
  | succ n ih => exact R_nonneg hμ0 ih z

lemma U_FS (y : X) (N : ℕ) : FS (U μ y N) := FS.finset_sum _ fun n => qlaw_FS y n

lemma U_nonneg (hμ0 : ∀ g, 0 ≤ μ g) (y : X) (N : ℕ) (z : X) : 0 ≤ U μ y N z :=
  Finset.sum_nonneg fun n _ => qlaw_nonneg hμ0 y n z

lemma U_sub_R (y : X) (N : ℕ) (z : X) :
    U μ y N z - R μ (U μ y N) z = qlaw μ y 0 z - qlaw μ y N z := by
  unfold U
  rw [R_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_range_sub' (fun n => qlaw μ y n z) N

/-- `B_μ(f, f) = 2 ⟨f, f⟩ - 2 ⟨f, R f⟩` for probabilities. -/
lemma B_diag (hμ : ThompsonAmenability.IsProbability μ) {f : X → ℝ} (hf : FS f) :
    B μ f f = 2 * ip f f - 2 * ip f (R μ f) := by
  have hT : ∀ g : G, ∑' z, (f z - f (g • z)) * (f z - f (g • z)) =
      2 * ip f f - 2 * ∑' z, f z * f (g • z) := by
    intro g
    have h1 : HasSum (fun z => f z * f z) (ip f f) := (hf.mul_right f).summable.hasSum
    have h2 : HasSum (fun z => f (g • z) * f (g • z)) (ip f f) :=
      hasSum_smul_comp (φ := fun z => f z * f z) g h1
    have h3 : HasSum (fun z => f z * f (g • z)) (∑' z, f z * f (g • z)) :=
      (hf.mul_right _).summable.hasSum
    have := ((h1.add h2).sub (h3.mul_left 2))
    refine (this.congr_fun ?_).tsum_eq.trans (by ring)
    intro z; ring
  unfold B
  simp_rw [hT]
  have hP : ip f (R μ f) = ∑ g ∈ μ.support, μ g * ∑' z, f z * f (g • z) := by
    unfold ip R
    simp_rw [Finset.mul_sum]
    have e : ∀ w, ∑ g ∈ μ.support, f w * (μ g * f (g • w)) =
        ∑ g ∈ μ.support, μ g * (f w * f (g • w)) := fun w =>
      Finset.sum_congr rfl fun g _ => by ring
    simp_rw [e]
    rw [tsum_sum_mul _ _ _ (fun g _ => (hf.mul_right _).summable)]
  rw [hP, Finset.mul_sum]
  have e2 : ∑ x ∈ μ.support, μ x * (2 * ip f f - 2 * ∑' z, f z * f (x • z)) =
      2 * ip f f * ∑ x ∈ μ.support, μ x -
        ∑ x ∈ μ.support, 2 * (μ x * ∑' z, f z * f (x • z)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [e2, mass_one hμ, mul_one]

lemma ip_delta' (f : X → ℝ) (y : X) : ip f (qlaw μ y 0) = f y := by
  unfold ip
  simp only [qlaw, mul_ite, mul_one, mul_zero]
  exact tsum_ite_eq y f

/-- The energy of the truncated Green function. -/
lemma B_U_le (hμ : ThompsonAmenability.IsProbability μ) (y : X) (N : ℕ) :
    B μ (U μ y N) (U μ y N) ≤ 2 * U μ y N y := by
  rw [B_diag hμ (U_FS y N)]
  have e : ip (U μ y N) (U μ y N) - ip (U μ y N) (R μ (U μ y N)) =
      U μ y N y - ip (U μ y N) (qlaw μ y N) := by
    unfold ip
    rw [← Summable.tsum_sub ((U_FS y N).mul_left _).summable
      ((R_FS μ (U_FS y N)).mul_left _).summable]
    have : ∀ z, U μ y N z * U μ y N z - U μ y N z * R μ (U μ y N) z =
        U μ y N z * qlaw μ y 0 z - U μ y N z * qlaw μ y N z := by
      intro z; rw [← mul_sub, ← mul_sub, U_sub_R]
    simp_rw [this]
    rw [Summable.tsum_sub ((qlaw_FS y 0).mul_left _).summable
      ((qlaw_FS y N).mul_left _).summable]
    have := ip_delta' (μ := μ) (U μ y N) y
    unfold ip at this
    rw [this]
  have : 0 ≤ ip (U μ y N) (qlaw μ y N) :=
    tsum_nonneg fun z => mul_nonneg (U_nonneg hμ.1 y N z) (qlaw_nonneg hμ.1 y N z)
  linarith

/-- A Hardy inequality at `y` and at `a` bounds the Green function from `y` at `a`. -/
lemma U_bdd (hμ : ThompsonAmenability.IsProbability μ) (y a : X)
    {C1 C2 : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (h1 : ∀ f : X → ℝ, FS f → f y ^ 2 ≤ C1 * B μ f f)
    (h2 : ∀ f : X → ℝ, FS f → f a ^ 2 ≤ C2 * B μ f f) (N : ℕ) :
    U μ y N a ^ 2 ≤ 4 * C1 * C2 := by
  have hB := B_U_le hμ y N
  have hy := h1 _ (U_FS (μ := μ) y N)
  have ha := h2 _ (U_FS (μ := μ) y N)
  have hy0 := U_nonneg hμ.1 y N y
  have hUy : U μ y N y ≤ 2 * C1 := by
    rcases hy0.lt_or_eq with hpos | hz
    · have : U μ y N y ^ 2 ≤ 2 * C1 * U μ y N y := by nlinarith
      nlinarith
    · rw [← hz]; linarith
  nlinarith

lemma summable_qlaw (hμ : ThompsonAmenability.IsProbability μ)
    (hH : ∀ o : X, ∃ C, 0 ≤ C ∧ ∀ f : X → ℝ, FS f → f o ^ 2 ≤ C * B μ f f) (y a : X) :
    Summable fun n => qlaw μ y n a := by
  obtain ⟨C1, hC1, h1⟩ := hH y
  obtain ⟨C2, hC2, h2⟩ := hH a
  refine summable_of_sum_range_le (c := Real.sqrt (4 * C1 * C2))
    (fun n => qlaw_nonneg hμ.1 y n a) fun N => ?_
  have := U_bdd hμ y a hC1 hC2 h1 h2 N
  have h0 := U_nonneg hμ.1 y N a
  exact Real.le_sqrt_of_sq_le this

end Green

/-! ## Hardy inequalities by comparison with `ℤ³` -/

section Compare

variable {G X : Type*} [Group G] [MulAction G X]

lemma mem_S6_of_μ3 {g : Equiv.Perm X3} (hg : g ∈ μ3.support) : ∃ v ∈ S6, Equiv.addRight v = g := by
  by_contra hc
  push Not at hc
  apply Finsupp.mem_support_iff.1 hg
  rw [μ3_apply]
  exact Finset.sum_eq_zero fun v hv => if_neg (hc v hv)

theorem hardy_of_Z3 {μ : G →₀ ℝ} (hμ0 : ∀ g, 0 ≤ μ g) (hnd : IsNondegenerate μ)
    (φ : X3 → X) (hφ : Function.Injective φ) (gv : X3 → G)
    (hgv : ∀ v z, φ (z + v) = gv v • φ z) :
    ∃ C, 0 ≤ C ∧ ∀ f : X → ℝ, FS f → f (φ 0) ^ 2 ≤ C * B μ f f := by
  obtain ⟨C3, hC3, h3⟩ := hardy_Z3
  choose Cv hCv0 hCv using fun v : X3 => Dg_le_B (X := X) hμ0 hnd (gv v)
  set K := ∑ v ∈ S6, Cv v
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun v _ => hCv0 v
  refine ⟨C3 * K, mul_nonneg hC3 hK0, fun f hf => ?_⟩
  have hF : FS (f ∘ φ) := hf.preimage hφ.injOn
  have hmain := h3 (f ∘ φ) hF
  -- each translation's Dirichlet form is controlled
  have hD : ∀ v ∈ S6, Dg (f ∘ φ) (Equiv.addRight v) ≤ K * B μ f f := by
    intro v hv
    have e : Dg (f ∘ φ) (Equiv.addRight v) = ∑' z, (fun w => (f w - f (gv v • w)) ^ 2) (φ z) := by
      unfold Dg
      refine tsum_congr fun z => ?_
      simp only [Function.comp, Equiv.Perm.smul_def, Equiv.coe_addRight, hgv]
    have hle : Dg (f ∘ φ) (Equiv.addRight v) ≤ Dg f (gv v) := by
      rw [e]
      exact tsum_comp_le_tsum_of_inj (hf.sq_diff (gv v)).summable (fun _ => sq_nonneg _) hφ
    have hCK : Cv v ≤ K := Finset.single_le_sum (fun w _ => hCv0 w) hv
    have := hCv v f hf
    have hB := B_self_nonneg hμ0 f
    nlinarith
  have hB3 : B μ3 (f ∘ φ) (f ∘ φ) ≤ K * B μ f f := by
    rw [B_self]
    calc ∑ g ∈ μ3.support, μ3 g * Dg (f ∘ φ) g
        ≤ ∑ g ∈ μ3.support, μ3 g * (K * B μ f f) := by
          refine Finset.sum_le_sum fun g hg => ?_
          obtain ⟨v, hv, rfl⟩ := mem_S6_of_μ3 hg
          exact mul_le_mul_of_nonneg_left (hD v hv) (μ3_nonneg _)
      _ = K * B μ f f := by
          rw [← Finset.sum_mul]
          have : ∑ g ∈ μ3.support, μ3 g = 1 := mass_one μ3_prob
          rw [this, one_mul]
  have : (f ∘ φ) 0 = f (φ 0) := rfl
  rw [this] at hmain
  calc f (φ 0) ^ 2 ≤ C3 * B μ3 (f ∘ φ) (f ∘ φ) := hmain
    _ ≤ C3 * (K * B μ f f) := mul_le_mul_of_nonneg_left hB3 hC3
    _ = C3 * K * B μ f f := by ring

end Compare

end JMMS.IETT110

/-! # Theorem 1.10, part D: left-continuous versions and the cocycle `τ`
(adapted from the proved solution of JMMS Proposition 5.3), and a one-sided limit lemma. -/

open IntervalExchange
open Filter Topology

namespace JMMS
namespace IETT110


local notation "C" => UnitAddCircle

lemma contMk : Continuous (fun t : ℝ => (t : C)) := continuous_quotient_mk'

/-- A function continuous within `s` at `a` with values in a finite set is eventually constant. -/
lemma eventually_eq_of_finite {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [T1Space β]
    {f : α → β} {s : Set α} {a : α} {S : Set β} (hS : S.Finite) (hf : ∀ t, f t ∈ S)
    (hc : ContinuousWithinAt f s a) : ∀ᶠ t in 𝓝[s] a, f t = f a := by
  have hopen : IsOpen (S \ {f a})ᶜ := ((hS.subset Set.sdiff_subset).isClosed).isOpen_compl
  have hmem : f a ∈ (S \ {f a})ᶜ := by simp
  filter_upwards [hc (hopen.mem_nhds hmem)] with t ht
  by_contra hne
  exact ht ⟨hf t, hne⟩

/-- `g` agrees with the translation `x + t ↦ y + t` just to the left of `x`: `y` is the left
limit of `g` at `x`. -/
def LeftLim (g : C → C) (x y : C) : Prop :=
  ∀ᶠ t : ℝ in 𝓝[<] (0:ℝ), g (x + (t : C)) = y + t

lemma leftLim_unique {g : C → C} {x y z : C} (h1 : LeftLim g x y) (h2 : LeftLim g x z) :
    y = z := by
  obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
  rw [ht1] at ht2
  exact add_right_cancel ht2

lemma leftLim_comp {g h : C → C} {x y z : C} (hh : LeftLim h x y) (hg : LeftLim g y z) :
    LeftLim (g ∘ h) x z := by
  filter_upwards [hh, hg] with t h1 h2
  simp only [Function.comp, h1, h2]

lemma leftLim_id (x : C) : LeftLim id x x := Eventually.of_forall fun _ => rfl

lemma leftLim_of_continuousAt {g : C → C} (ha : (angles g).Finite) {x : C}
    (hc : ContinuousAt g x) : LeftLim g x (g x) := by
  have hU : ∀ᶠ z in 𝓝 x, g z - z = g x - x := by
    have := eventually_eq_of_finite (s := Set.univ) ha (fun t => ⟨t, rfl⟩)
      ((hc.sub continuousAt_id).continuousWithinAt)
    simpa [nhdsWithin_univ] using this
  have ht : Tendsto (fun t : ℝ => x + (t : C)) (𝓝[<] 0) (𝓝 x) := by
    have : Tendsto (fun t : ℝ => x + (t : C)) (𝓝 0) (𝓝 x) :=
      (continuous_const.add contMk).tendsto' 0 x (by simp)
    exact this.mono_left nhdsWithin_le_nhds
  filter_upwards [ht hU] with t ht
  have : g (x + t) = (g (x + t) - (x + t)) + (x + t) := by abel
  rw [this, ht]; abel

/-- Points just to the left of `x` avoid a given finite set. -/
lemma eventually_not_mem {D : Set C} (hD : D.Finite) (x : C) :
    ∀ᶠ t : ℝ in 𝓝[<] (0:ℝ), x + (t : C) ∉ D := by
  have hD' : IsClosed (D \ {x}) := (hD.subset Set.sdiff_subset).isClosed
  have h1 : ∀ᶠ t : ℝ in 𝓝 (0:ℝ), x + (t : C) ∉ D \ {x} := by
    have hc : ContinuousAt (fun t : ℝ => x + (t : C)) 0 := (continuous_const.add contMk).continuousAt
    have hx : x + ((0:ℝ) : C) ∉ D \ {x} := by simp
    exact hc.eventually (hD'.isOpen_compl.mem_nhds hx)
  have h2 : ∀ᶠ t : ℝ in 𝓝[<] (0:ℝ), t ∈ Set.Ioo (-1 : ℝ) 0 :=
    Ioo_mem_nhdsLT (by norm_num)
  filter_upwards [nhdsWithin_le_nhds h1, h2] with t ht ht2 hmem
  apply ht
  refine ⟨hmem, ?_⟩
  intro heq
  have h0 : ((t : ℝ) : C) = 0 := by
    have : x + (t : C) = x + 0 := by simpa using heq
    exact add_left_cancel this
  rw [AddCircle.coe_eq_zero_iff] at h0
  obtain ⟨n, hn⟩ := h0
  simp only [zsmul_eq_mul, mul_one] at hn
  obtain ⟨h3, h4⟩ := ht2
  rw [← hn] at h3 h4
  have : (-1 : ℤ) < n := by exact_mod_cast h3
  have : n < 0 := by exact_mod_cast h4
  omega

lemma leftLim_exists {g : Equiv.Perm C} (hg : IsIntervalExchange g) (x : C) :
    ∃ y, LeftLim g x y := by
  obtain ⟨-, ha, hd⟩ := hg
  have hev := eventually_not_mem hd x
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev
  have hl' : l < 0 := hl
  set f : ℝ → C := fun t => g (x + (t : C)) - (x + (t : C)) with hf
  have hcont : ContinuousOn f (Set.Ioo l 0) := by
    intro s hs
    have hgc : ContinuousAt g (x + (s : C)) := by
      have := hsub hs
      simpa using this
    have h1 : ContinuousAt (fun t : ℝ => x + (t : C)) s :=
      (continuous_const.add contMk).continuousAt
    exact ((hgc.comp_of_eq h1 rfl).sub h1).continuousWithinAt
  have hdisc : IsDiscrete (angles (⇑g)) := by
    rw [isDiscrete_iff_discreteTopology]
    have : Finite (angles (⇑g)) := ha.to_subtype
    infer_instance
  have hconst : ∀ s ∈ Set.Ioo l 0, f s = f (l / 2) := by
    intro s hs
    refine isPreconnected_Ioo.constant_of_mapsTo hdisc hcont ?_ hs ?_
    · intro t _; exact ⟨_, rfl⟩
    · constructor <;> linarith
  refine ⟨x + f (l / 2), ?_⟩
  filter_upwards [Ioo_mem_nhdsLT hl] with t ht
  rw [← hconst t ht, hf]
  simp only
  abel

/-- The left-continuous version of `g`. -/
noncomputable def tl (g : C → C) (x : C) : C :=
  open Classical in if h : ∃ y, LeftLim g x y then h.choose else x

lemma tl_spec {g : Equiv.Perm C} (hg : g ∈ IET) (x : C) : LeftLim g x (tl g x) := by
  have h := leftLim_exists ((mem_IET_iff g).1 hg) x
  rw [tl, dif_pos h]
  exact h.choose_spec

lemma tl_eq {g : Equiv.Perm C} (hg : g ∈ IET) {x y : C} (h : LeftLim g x y) : tl g x = y :=
  leftLim_unique (tl_spec hg x) h

lemma tl_mul {g h : Equiv.Perm C} (hg : g ∈ IET) (hh : g ∈ IET → h ∈ IET) (x : C) :
    tl (⇑(g * h)) x = tl g (tl h x) := by
  have hh' := hh hg
  apply tl_eq (IET.mul_mem hg hh')
  rw [Equiv.Perm.coe_mul]
  exact leftLim_comp (tl_spec hh' x) (tl_spec hg _)

lemma tl_one (x : C) : tl (⇑(1 : Equiv.Perm C)) x = x :=
  tl_eq IET.one_mem (leftLim_id x)

lemma tl_eq_self {g : Equiv.Perm C} (hg : g ∈ IET) {x : C} (hc : ContinuousAt g x) :
    tl g x = g x :=
  tl_eq hg (leftLim_of_continuousAt ((mem_IET_iff g).1 hg).2.1 hc)

/-- The left-continuous version of an element of `IET`, as a permutation. -/
noncomputable def tlPerm (g : IET) : Equiv.Perm C where
  toFun := tl (g : Equiv.Perm C)
  invFun := tl ((g⁻¹ : IET) : Equiv.Perm C)
  left_inv x := by
    rw [← tl_mul (g⁻¹ : IET).2 (fun _ => g.2), ← Subgroup.coe_mul, inv_mul_cancel,
      Subgroup.coe_one, tl_one]
  right_inv x := by
    rw [← tl_mul g.2 (fun _ => (g⁻¹ : IET).2), ← Subgroup.coe_mul, mul_inv_cancel,
      Subgroup.coe_one, tl_one]

/-- `g ↦ g̃` is a homomorphism. -/
noncomputable def tlHom : IET →* Equiv.Perm C where
  toFun := tlPerm
  map_one' := by ext x; exact tl_one x
  map_mul' g h := by ext x; exact tl_mul g.2 (fun _ => h.2) x

lemma tlHom_apply (g : IET) (x : C) : tlHom g x = tl (g : Equiv.Perm C) x := rfl

/-- The cocycle `τ_g = g̃ g⁻¹`. -/
noncomputable def τ (g : IET) : Equiv.Perm C := tlHom g * (g : Equiv.Perm C)⁻¹

lemma τ_mul (g h : IET) :
    τ (g * h) = τ g * ((g : Equiv.Perm C) * τ h * (g : Equiv.Perm C)⁻¹) := by
  simp only [τ, map_mul, Subgroup.coe_mul, mul_inv_rev]
  group

lemma τ_support_finite (g : IET) : {y | τ g y ≠ y}.Finite := by
  have hd := ((mem_IET_iff _).1 g.2).2.2
  refine (hd.image (g : Equiv.Perm C)).subset ?_
  intro y hy
  refine ⟨(g : Equiv.Perm C)⁻¹ y, ?_, by simp⟩
  intro hc
  apply hy
  show tl (g : Equiv.Perm C) ((g : Equiv.Perm C)⁻¹ y) = y
  rw [tl_eq_self g.2 hc]
  simp

/-- `τ_g = 1` forces `g` to be a rotation. -/
lemma rotation_of_τ_eq_one (g : IET) (h : τ g = 1) :
    ∃ c : C, ∀ z, (g : Equiv.Perm C) z = z + c := by
  have hie := (mem_IET_iff _).1 g.2
  have htl : ∀ x, tl (g : Equiv.Perm C) x = (g : Equiv.Perm C) x := by
    intro x
    have := congrArg (fun π : Equiv.Perm C => π ((g : Equiv.Perm C) x)) h
    simpa [τ, tlHom_apply] using this
  -- local translation on both sides
  have hloc : ∀ x : C, ∀ᶠ t : ℝ in 𝓝 (0:ℝ),
      (g : Equiv.Perm C) (x + (t : C)) = (g : Equiv.Perm C) x + t := by
    intro x
    rw [← nhdsLT_sup_nhdsGE]
    refine Filter.eventually_sup.2 ⟨?_, ?_⟩
    · have := tl_spec g.2 x
      rw [htl] at this
      exact this
    · have hc : ContinuousWithinAt
          (fun t : ℝ => (g : Equiv.Perm C) (x + (t : C)) - (x + (t : C))) (Set.Ici 0) 0 :=
        (hie.1 x).sub ((continuous_const.add contMk).continuousWithinAt)
      filter_upwards [eventually_eq_of_finite hie.2.1 (fun t : ℝ => ⟨x + (t : C), rfl⟩) hc] with t ht
      simp only [QuotientAddGroup.mk_zero, add_zero] at ht
      rw [← sub_add_cancel ((g : Equiv.Perm C) (x + t)) (x + t), ht]
      abel
  set f : ℝ → C := fun u => (g : Equiv.Perm C) u - u with hf
  have hlc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro s
    have ht : Tendsto (fun u : ℝ => u - s) (𝓝 s) (𝓝 0) := by
      exact (continuous_id.sub continuous_const).tendsto' s 0 (by simp)
    filter_upwards [ht (hloc (s : C))] with u hu
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hu
    simp only [hf]
    have e : ((s : ℝ) : C) + ((u - s : ℝ) : C) = (u : C) := by
      rw [← QuotientAddGroup.mk_add]; congr 1; ring
    rw [e] at hu
    rw [hu]
    have e2 : (u : C) = (s : C) + ((u - s : ℝ) : C) := e.symm
    conv_lhs => rw [e2]
    abel
  refine ⟨f 0, fun z => ?_⟩
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective z
  have := hlc.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ u) (Set.mem_univ 0)
  have e : (g : Equiv.Perm C) (u : C) = (u : C) + f u := by simp [hf]
  rw [e, this]


lemma τ_apply_smul (g : IET) (u : C) : τ g ((g : Equiv.Perm C) u) = tl (g : Equiv.Perm C) u := by
  simp [τ, tlHom_apply]

lemma τ_eq_one_of_continuous (g : IET) (hc : Continuous (g : Equiv.Perm C)) : τ g = 1 := by
  ext z
  obtain ⟨u, rfl⟩ : ∃ u, (g : Equiv.Perm C) u = z := ⟨(g : Equiv.Perm C).symm z, by simp⟩
  rw [τ_apply_smul, tl_eq_self g.2 hc.continuousAt]
  rfl

lemma tl_sub_mem (Λ : AddSubgroup C) {g : Equiv.Perm C} (hg : g ∈ IET) (hΛ : ∀ x, g x - x ∈ Λ)
    (u : C) : tl g u - u ∈ Λ := by
  obtain ⟨t, ht⟩ := (tl_spec hg u).exists
  have := hΛ (u + t)
  rw [ht] at this
  convert this using 1; abel

lemma τ_sub_mem (Λ : AddSubgroup C) (g : IET) (hΛ : ∀ x, (g : Equiv.Perm C) x - x ∈ Λ)
    (z : C) : τ g z - z ∈ Λ := by
  obtain ⟨u, rfl⟩ : ∃ u, (g : Equiv.Perm C) u = z := ⟨(g : Equiv.Perm C).symm z, by simp⟩
  rw [τ_apply_smul]
  have h1 := tl_sub_mem Λ g.2 hΛ u
  have h2 := hΛ u
  have := Λ.sub_mem h1 h2
  convert this using 1; abel

/-- Points just to the right of `x` avoid a given finite set. -/
lemma eventually_not_mem_right {D : Set C} (hD : D.Finite) (x : C) :
    ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), x + (t : C) ∉ D := by
  have hD' : IsClosed (D \ {x}) := (hD.subset Set.sdiff_subset).isClosed
  have h1 : ∀ᶠ t : ℝ in 𝓝 (0:ℝ), x + (t : C) ∉ D \ {x} := by
    have hc : ContinuousAt (fun t : ℝ => x + (t : C)) 0 := (continuous_const.add contMk).continuousAt
    have hx : x + ((0:ℝ) : C) ∉ D \ {x} := by simp
    exact hc.eventually (hD'.isOpen_compl.mem_nhds hx)
  have h2 : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), t ∈ Set.Ioo (0 : ℝ) 1 :=
    Ioo_mem_nhdsGT (by norm_num)
  filter_upwards [nhdsWithin_le_nhds h1, h2] with t ht ht2 hmem
  apply ht
  refine ⟨hmem, ?_⟩
  intro heq
  have h0 : ((t : ℝ) : C) = 0 := by
    have : x + (t : C) = x + 0 := by simpa using heq
    exact add_left_cancel this
  rw [AddCircle.coe_eq_zero_iff] at h0
  obtain ⟨n, hn⟩ := h0
  simp only [zsmul_eq_mul, mul_one] at hn
  obtain ⟨h3, h4⟩ := ht2
  rw [← hn] at h3 h4
  have : (0 : ℤ) < n := by exact_mod_cast h3
  have : n < 1 := by exact_mod_cast h4
  omega

/-- A dense subgroup has elements represented by arbitrarily small positive reals. -/
lemma exists_small_pos {Λ : AddSubgroup C} (hd : Dense (Λ : Set C)) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < ε ∧ (t : C) ∈ Λ := by
  have hopen : IsOpen ((fun t : ℝ => (t : C)) '' Set.Ioo 0 ε) :=
    QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  obtain ⟨c, hcΛ, hc⟩ := hd.exists_mem_open hopen ⟨((ε / 2 : ℝ) : C), ε / 2,
    ⟨by linarith, by linarith⟩, rfl⟩
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hc
  exact ⟨t, ht0, ht1, hcΛ⟩

/-- If `g̃ (u + a + δ) = g (u + a) + δ` for every `a` in a dense subgroup, then `g̃` and `g`
agree at `u + δ`. -/
lemma tl_eq_of_shift {g : Equiv.Perm C} (hg : g ∈ IET) {Λ : AddSubgroup C}
    (hd : Dense (Λ : Set C)) (u δ : C) (h : ∀ a ∈ Λ, tl g (u + a + δ) = g (u + a) + δ) :
    tl g (u + δ) = g (u + δ) := by
  have hie := (mem_IET_iff g).1 hg
  set L := 𝓝[Set.Ioi 0 ∩ {t : ℝ | (t : C) ∈ Λ}] (0 : ℝ)
  have hL : L.NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨t, ht0, ht1, htΛ⟩ := exists_small_pos hd hε
    refine ⟨t, ⟨ht0, htΛ⟩, ?_⟩
    rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos ht0]
    exact ht1
  have hLle : L ≤ 𝓝[Set.Ici 0] (0 : ℝ) :=
    nhdsWithin_mono _ fun t ht => Set.mem_Ici.2 (le_of_lt ht.1)
  have hLle' : L ≤ 𝓝[>] (0 : ℝ) := nhdsWithin_mono _ fun t ht => ht.1
  have t1 : Tendsto (fun t : ℝ => g (u + δ + (t : C))) L (𝓝 (g (u + δ))) := by
    have := (hie.1 (u + δ)).tendsto
    simp only [QuotientAddGroup.mk_zero, add_zero] at this
    exact this.mono_left hLle
  have t2 : Tendsto (fun t : ℝ => g (u + (t : C)) + δ) L (𝓝 (g u + δ)) := by
    have := (hie.1 u).tendsto
    simp only [QuotientAddGroup.mk_zero, add_zero] at this
    exact (this.mono_left hLle).add_const δ
  have hev : ∀ᶠ t : ℝ in L, g (u + δ + (t : C)) = g (u + (t : C)) + δ := by
    have h1 : ∀ᶠ t : ℝ in L, u + δ + (t : C) ∉ {x | ¬ ContinuousAt g x} :=
      hLle' (eventually_not_mem_right hie.2.2 (u + δ))
    have h2 : ∀ᶠ t : ℝ in L, t ∈ Set.Ioi 0 ∩ {t : ℝ | (t : C) ∈ Λ} := self_mem_nhdsWithin
    filter_upwards [h1, h2] with t ht1 ht2
    have hc : ContinuousAt g (u + δ + (t : C)) := by simpa using ht1
    rw [← tl_eq_self hg hc, ← h _ ht2.2]
    congr 1; abel
  have heq : g (u + δ) = g u + δ := tendsto_nhds_unique (t1.congr' hev) t2
  have h0 := h 0 Λ.zero_mem
  simp only [add_zero] at h0
  rw [h0, heq]

end IETT110
end JMMS

/-! # Theorem 1.10, part E: bounded harmonic functions from an eventually constant label

For a finitely supported probability `μ` on `G` and a labelling `T : G → Y`, let `V h = 1` if some
step `s ∈ supp μ` changes the label (`T (h s) ≠ T h`), else `0`. If the expected number of such
"label changes" along the walk is finite (`∑_n Mⁿ V g < ∞`), then `P_n(g, A) = Mⁿ 1_{T ∈ A} (g)`
converges to a bounded harmonic function of `g`. If all these are constant, the limit law of the
label is a point mass (a 0–1 law, proved with the operator `M` only). -/

open IntervalExchange Filter Topology

set_option linter.unusedSectionVars false

namespace JMMS.IETT110

open Classical

section Boundary

variable {G : Type*} [Group G] {Y : Type*}

/-- The Markov operator `M f g = ∑_s μ(s) f(g s)`. -/
noncomputable def Mop (μ : G →₀ ℝ) (f : G → ℝ) (g : G) : ℝ :=
  ∑ s ∈ μ.support, μ s * f (g * s)

variable {μ : G →₀ ℝ}

lemma Mop_add (f h : G → ℝ) : Mop μ (fun x => f x + h x) = fun x => Mop μ f x + Mop μ h x := by
  funext x; unfold Mop; rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

lemma Mop_smul (c : ℝ) (f : G → ℝ) : Mop μ (fun x => c * f x) = fun x => c * Mop μ f x := by
  funext x; unfold Mop; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

lemma Mop_sub (f h : G → ℝ) : Mop μ (fun x => f x - h x) = fun x => Mop μ f x - Mop μ h x := by
  funext x; unfold Mop; rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

lemma Mop_const (hμ : ThompsonAmenability.IsProbability μ) (c : ℝ) :
    Mop μ (fun _ => c) = fun _ => c := by
  funext x; unfold Mop
  rw [← Finset.sum_mul]
  have : ∑ s ∈ μ.support, μ s = 1 := by simpa [Finsupp.sum] using hμ.2
  rw [this, one_mul]

lemma Mop_mono (hμ : ThompsonAmenability.IsProbability μ) {f h : G → ℝ} (hfh : ∀ x, f x ≤ h x) (x : G) :
    Mop μ f x ≤ Mop μ h x :=
  Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hfh _) (hμ.1 s)

lemma iter_add (n : ℕ) (f h : G → ℝ) :
    (Mop μ)^[n] (fun x => f x + h x) = fun x => (Mop μ)^[n] f x + (Mop μ)^[n] h x := by
  induction n generalizing f h with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply]
    rw [Mop_add, ih]

lemma iter_smul (n : ℕ) (c : ℝ) (f : G → ℝ) :
    (Mop μ)^[n] (fun x => c * f x) = fun x => c * (Mop μ)^[n] f x := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply]
    rw [Mop_smul, ih]

lemma iter_sub (n : ℕ) (f h : G → ℝ) :
    (Mop μ)^[n] (fun x => f x - h x) = fun x => (Mop μ)^[n] f x - (Mop μ)^[n] h x := by
  induction n generalizing f h with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply]
    rw [Mop_sub, ih]

lemma iter_sum {ι : Type*} (n : ℕ) (s : Finset ι) (F : ι → G → ℝ) :
    (Mop μ)^[n] (fun x => ∑ i ∈ s, F i x) = fun x => ∑ i ∈ s, (Mop μ)^[n] (F i) x := by
  induction s using Finset.induction_on with
  | empty =>
    have := iter_smul (μ := μ) n 0 (fun _ => 0)
    simp only [zero_mul] at this
    simpa using this
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    rw [iter_add, ih]

lemma iter_const (hμ : ThompsonAmenability.IsProbability μ) (n : ℕ) (c : ℝ) :
    (Mop μ)^[n] (fun _ => c) = fun _ => c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Mop_const hμ, ih]

lemma iter_mono (hμ : ThompsonAmenability.IsProbability μ) (n : ℕ) {f h : G → ℝ}
    (hfh : ∀ x, f x ≤ h x) (x : G) : (Mop μ)^[n] f x ≤ (Mop μ)^[n] h x := by
  induction n generalizing f h with
  | zero => exact hfh x
  | succ n ih =>
    simp only [Function.iterate_succ_apply]
    exact ih (Mop_mono hμ hfh)

lemma iter_abs_le (hμ : ThompsonAmenability.IsProbability μ) (n : ℕ) {f h : G → ℝ}
    (hfh : ∀ x, |f x| ≤ h x) (x : G) : |(Mop μ)^[n] f x| ≤ (Mop μ)^[n] h x := by
  rw [abs_le]
  constructor
  · have := iter_mono hμ n (f := fun x => -h x) (h := f) (fun x => (abs_le.1 (hfh x)).1) x
    have e := iter_smul (μ := μ) n (-1) h
    simp only [neg_one_mul] at e
    rw [e] at this
    linarith
  · exact iter_mono hμ n (fun x => (abs_le.1 (hfh x)).2) x

lemma iter_tendsto (n : ℕ) {F : ℕ → G → ℝ} {f : G → ℝ}
    (hF : ∀ x, Tendsto (fun j => F j x) atTop (𝓝 (f x))) (x : G) :
    Tendsto (fun j => (Mop μ)^[n] (F j) x) atTop (𝓝 ((Mop μ)^[n] f x)) := by
  induction n generalizing F f with
  | zero => exact hF x
  | succ n ih =>
    simp only [Function.iterate_succ_apply]
    refine ih (fun y => ?_)
    unfold Mop
    exact tendsto_finsetSum _ fun s _ => (hF _).const_mul _

lemma iter_left (n : ℕ) (f : G → ℝ) (g x : G) :
    (Mop μ)^[n] f (g * x) = (Mop μ)^[n] (fun y => f (g * y)) x := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply]
    rw [ih]
    have : (fun y => Mop μ f (g * y)) = Mop μ (fun y => f (g * y)) := by
      funext y; unfold Mop; simp only [mul_assoc]
    rw [this]

/-- The points reachable in `n` steps from `x`. -/
noncomputable def reach (μ : G →₀ ℝ) (x : G) : ℕ → Finset G
  | 0 => {x}
  | n + 1 => (reach μ x n).biUnion fun h => μ.support.image (h * ·)

lemma iter_congr (n : ℕ) {f f' : G → ℝ} (x : G) (h : ∀ y ∈ reach μ x n, f y = f' y) :
    (Mop μ)^[n] f x = (Mop μ)^[n] f' x := by
  induction n generalizing f f' with
  | zero => exact h x (by simp [reach])
  | succ n ih =>
    simp only [Function.iterate_succ_apply]
    refine ih fun y hy => ?_
    unfold Mop
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [h]
    exact Finset.mem_biUnion.2 ⟨y, hy, Finset.mem_image.2 ⟨s, hs, rfl⟩⟩

variable (μ) (T : G → Y)

/-- `V h = 1` iff some step changes the label. -/
noncomputable def Vf (h : G) : ℝ := if ∃ s ∈ μ.support, T (h * s) ≠ T h then 1 else 0

/-- The indicator of `T h ∈ A`. -/
noncomputable def ind (A : Set Y) (h : G) : ℝ := if T h ∈ A then 1 else 0

/-- The probability that the label after `n` steps from `g` is in `A`. -/
noncomputable def Pn (n : ℕ) (g : G) (A : Set Y) : ℝ := (Mop μ)^[n] (ind T A) g

variable {μ T}

lemma Vf_nonneg (h : G) : 0 ≤ Vf μ T h := by unfold Vf; split_ifs <;> norm_num

lemma ind_nonneg (A : Set Y) (h : G) : 0 ≤ ind T A h := by unfold ind; split_ifs <;> norm_num

lemma ind_le_one (A : Set Y) (h : G) : ind T A h ≤ 1 := by unfold ind; split_ifs <;> norm_num

variable (hμ : ThompsonAmenability.IsProbability μ)
include hμ

lemma Pn_nonneg (n : ℕ) (g : G) (A : Set Y) : 0 ≤ Pn μ T n g A := by
  have := iter_mono hμ n (f := fun _ => 0) (h := ind T A) (fun x => ind_nonneg A x) g
  rwa [iter_const hμ] at this

lemma Pn_le_one (n : ℕ) (g : G) (A : Set Y) : Pn μ T n g A ≤ 1 := by
  have := iter_mono hμ n (f := ind T A) (h := fun _ => 1) (fun x => ind_le_one A x) g
  rwa [iter_const hμ] at this

lemma Mop_ind_sub (A : Set Y) (h : G) : |Mop μ (ind T A) h - ind T A h| ≤ Vf μ T h := by
  have hsum : ∑ s ∈ μ.support, μ s = 1 := by simpa [Finsupp.sum] using hμ.2
  have e : Mop μ (ind T A) h - ind T A h = ∑ s ∈ μ.support, μ s * (ind T A (h * s) - ind T A h) := by
    unfold Mop
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  rw [e]
  unfold Vf
  split_ifs with hc
  · calc |∑ s ∈ μ.support, μ s * (ind T A (h * s) - ind T A h)|
        ≤ ∑ s ∈ μ.support, |μ s * (ind T A (h * s) - ind T A h)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ μ.support, μ s * 1 := by
          refine Finset.sum_le_sum fun s _ => ?_
          rw [abs_mul, abs_of_nonneg (hμ.1 s)]
          refine mul_le_mul_of_nonneg_left ?_ (hμ.1 s)
          have h1 := ind_nonneg (T := T) A (h * s)
          have h2 := ind_le_one (T := T) A (h * s)
          have h3 := ind_nonneg (T := T) A h
          have h4 := ind_le_one (T := T) A h
          rw [abs_le]; constructor <;> linarith
      _ = 1 := by rw [Finset.sum_congr rfl fun s _ => mul_one (μ s), hsum]
  · push Not at hc
    rw [Finset.sum_eq_zero fun s hs => by simp [ind, hc s hs]]
    simp

/-- One more step changes `Pₙ` by at most the expected number of label changes. -/
lemma Pn_step (n : ℕ) (g : G) (A : Set Y) :
    |Pn μ T (n + 1) g A - Pn μ T n g A| ≤ (Mop μ)^[n] (Vf μ T) g := by
  unfold Pn
  rw [Function.iterate_succ_apply]
  have := iter_sub (μ := μ) n (Mop μ (ind T A)) (ind T A)
  have e := congrFun this g
  rw [← e]
  exact iter_abs_le hμ n (fun x => Mop_ind_sub hμ A x) g

lemma iter_diff (j : ℕ) (A : Set Y) (h : G) :
    |(Mop μ)^[j] (ind T A) h - ind T A h| ≤ ∑ i ∈ Finset.range j, (Mop μ)^[i] (Vf μ T) h := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ]
    have := Pn_step (T := T) hμ j h A
    unfold Pn at this
    calc _ ≤ |(Mop μ)^[j + 1] (ind T A) h - (Mop μ)^[j] (ind T A) h| +
          |(Mop μ)^[j] (ind T A) h - ind T A h| := abs_sub_le _ _ _
      _ ≤ _ := by linarith

variable (hV : ∀ g, Summable fun n => (Mop μ)^[n] (Vf μ T) g)
include hV

lemma Pn_cauchy (g : G) (A : Set Y) : CauchySeq fun n => Pn μ T n g A :=
  cauchySeq_of_dist_le_of_summable _ (fun n => by
    rw [Real.dist_eq, abs_sub_comm]; exact Pn_step hμ n g A) (hV g)

/-- The limit `p(g, A)`. -/
noncomputable def plim (μ : G →₀ ℝ) (T : G → Y) (g : G) (A : Set Y) : ℝ :=
  limUnder atTop fun n => Pn μ T n g A

lemma tendsto_plim (g : G) (A : Set Y) :
    Tendsto (fun n => Pn μ T n g A) atTop (𝓝 (plim μ T g A)) :=
  (Pn_cauchy hμ hV g A).tendsto_limUnder

lemma plim_nonneg (g : G) (A : Set Y) : 0 ≤ plim μ T g A :=
  ge_of_tendsto' (tendsto_plim hμ hV g A) fun n => Pn_nonneg hμ n g A

lemma plim_le_one (g : G) (A : Set Y) : plim μ T g A ≤ 1 :=
  le_of_tendsto' (tendsto_plim hμ hV g A) fun n => Pn_le_one hμ n g A

lemma plim_harmonic (g : G) (A : Set Y) :
    plim μ T g A = ∑ s ∈ μ.support, μ s * plim μ T (g * s) A := by
  have h1 : Tendsto (fun n => Pn μ T (n + 1) g A) atTop (𝓝 (plim μ T g A)) :=
    (tendsto_plim hμ hV g A).comp (tendsto_add_atTop_nat 1)
  have e : ∀ n, Pn μ T (n + 1) g A = ∑ s ∈ μ.support, μ s * Pn μ T n (g * s) A := by
    intro n
    unfold Pn
    rw [Function.iterate_succ_apply']
    rfl
  simp_rw [e] at h1
  exact tendsto_nhds_unique h1
    (tendsto_finsetSum _ fun s _ => (tendsto_plim hμ hV (g * s) A).const_mul _)

lemma plim_finset (K : Finset Y) (g : G) :
    plim μ T g (K : Set Y) = ∑ k ∈ K, plim μ T g {k} := by
  have e : ∀ n, Pn μ T n g (K : Set Y) = ∑ k ∈ K, Pn μ T n g {k} := by
    intro n
    unfold Pn
    have : ind T (K : Set Y) = fun h => ∑ k ∈ K, ind T {k} h := by
      funext h
      unfold ind
      simp only [Finset.mem_coe, Set.mem_singleton_iff]
      rw [Finset.sum_ite_eq]
    rw [this, iter_sum]
  have h1 := tendsto_plim hμ hV g (K : Set Y)
  simp_rw [e] at h1
  exact tendsto_nhds_unique h1 (tendsto_finsetSum _ fun k _ => tendsto_plim hμ hV g {k})

/-- The tail of the expected number of label changes. -/
noncomputable def tail (μ : G →₀ ℝ) (T : G → Y) (n : ℕ) : ℝ :=
  ∑' i, (Mop μ)^[n + i] (Vf μ T) 1

lemma tail_tendsto : Tendsto (tail μ T) atTop (𝓝 0) := by
  have := (hV 1).tendsto_sum_tsum_nat
  have h2 : Tendsto (fun n => ∑' i, (Mop μ)^[i] (Vf μ T) 1 -
      ∑ i ∈ Finset.range n, (Mop μ)^[i] (Vf μ T) 1) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := ∑' i, (Mop μ)^[i] (Vf μ T) 1)).sub this
    simpa using this
  refine h2.congr fun n => ?_
  unfold tail
  rw [← (hV 1).sum_add_tsum_nat_add n]
  simp_rw [add_comm n]
  ring

omit hV in
lemma iter_Vf_nonneg (n : ℕ) (g : G) : 0 ≤ (Mop μ)^[n] (Vf μ T) g := by
  have := iter_mono hμ n (f := fun _ => 0) (h := Vf μ T) (fun x => Vf_nonneg x) g
  rwa [iter_const hμ] at this

lemma sum_le_tail (n j : ℕ) :
    ∑ i ∈ Finset.range j, (Mop μ)^[n + i] (Vf μ T) 1 ≤ tail μ T n := by
  have hs : Summable fun i => (Mop μ)^[n + i] (Vf μ T) 1 :=
    (summable_nat_add_iff n).2 (hV 1) |>.congr fun i => by rw [add_comm]
  exact hs.sum_le_tsum _ fun i _ => iter_Vf_nonneg hμ _ _

/-- The 0–1 law: if every `plim (·) A` is constant, its value is `0` or `1`. -/
lemma zero_one (hc : ∀ g A, plim μ T g A = plim μ T 1 A) (A : Set Y) :
    plim μ T 1 A = 0 ∨ plim μ T 1 A = 1 := by
  set c := plim μ T 1 A
  -- `J n j = Mⁿ (1_A · Mʲ 1_A)(1)`
  have hJ : ∀ n j, Pn μ T (n + j) 1 A - tail μ T n ≤
      (Mop μ)^[n] (fun h => ind T A h * (Mop μ)^[j] (ind T A) h) 1 := by
    intro n j
    have hpt : ∀ h, (Mop μ)^[j] (ind T A) h -
        ∑ i ∈ Finset.range j, (Mop μ)^[i] (Vf μ T) h ≤ ind T A h * (Mop μ)^[j] (ind T A) h := by
      intro h
      have hd := iter_diff (T := T) hμ j A h
      have hP0 := Pn_nonneg (T := T) hμ j h A
      unfold Pn ind at hP0
      unfold ind at hd ⊢
      split_ifs at hd ⊢
      · simp
        exact Finset.sum_nonneg fun i _ => iter_Vf_nonneg hμ i h
      · rw [sub_zero, abs_of_nonneg hP0] at hd
        simp only [zero_mul]; linarith
    have hm := iter_mono hμ n hpt 1
    rw [iter_sub, iter_sum] at hm
    simp only at hm
    have e1 : (Mop μ)^[n] ((Mop μ)^[j] (ind T A)) 1 = Pn μ T (n + j) 1 A := by
      unfold Pn; rw [Function.iterate_add_apply]
    have e2 : ∑ i ∈ Finset.range j, (Mop μ)^[n] ((Mop μ)^[i] (Vf μ T)) 1 =
        ∑ i ∈ Finset.range j, (Mop μ)^[n + i] (Vf μ T) 1 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Function.iterate_add_apply]
    rw [e1, e2] at hm
    have := sum_le_tail hμ hV n j
    linarith
  -- `j → ∞`
  have hlimj : ∀ n, Tendsto (fun j => (Mop μ)^[n] (fun h => ind T A h * (Mop μ)^[j] (ind T A) h) 1)
      atTop (𝓝 (c * Pn μ T n 1 A)) := by
    intro n
    have := iter_tendsto (μ := μ) n (F := fun j h => ind T A h * (Mop μ)^[j] (ind T A) h)
      (f := fun h => ind T A h * c) (fun h => by
        have := (tendsto_plim hμ hV h A).const_mul (ind T A h)
        rw [hc h A] at this
        exact this) 1
    have e : (Mop μ)^[n] (fun h => ind T A h * c) 1 = c * Pn μ T n 1 A := by
      have := iter_smul (μ := μ) n c (ind T A)
      unfold Pn
      rw [← congrFun this 1]
      rw [show (fun h => ind T A h * c) = (fun x => c * ind T A x) from
        funext fun h => mul_comm _ _]
    rwa [e] at this
  have hn : ∀ n, c - tail μ T n ≤ c * Pn μ T n 1 A := by
    intro n
    have h1 : Tendsto (fun j => Pn μ T (n + j) 1 A - tail μ T n) atTop (𝓝 (c - tail μ T n)) :=
      ((tendsto_plim hμ hV 1 A).comp (tendsto_atTop_atTop_of_monotone
        (fun a b hab => by omega) fun b => ⟨b, by omega⟩)).sub_const _
    exact le_of_tendsto_of_tendsto' h1 (hlimj n) (hJ n)
  have hfin : c - 0 ≤ c * c :=
    le_of_tendsto_of_tendsto' ((tendsto_const_nhds).sub (tail_tendsto hμ hV))
      ((tendsto_plim hμ hV 1 A).const_mul c) hn
  have h0 := plim_nonneg hμ hV 1 A
  have h1 := plim_le_one hμ hV 1 A
  by_contra hne
  push Not at hne
  have : 0 < c := lt_of_le_of_ne h0 (Ne.symm hne.1)
  have : c < 1 := lt_of_le_of_ne h1 hne.2
  nlinarith

/-- Under constancy, the limit law of the label is a point mass. -/
theorem exists_dirac (hc : ∀ g A, plim μ T g A = plim μ T 1 A) :
    ∃ y0, plim μ T 1 {y0} = 1 ∧ ∀ y, plim μ T 1 {y} = 1 → y = y0 := by
  obtain ⟨n, hn⟩ := ((tail_tendsto hμ hV).eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))).exists
  set K := (reach μ 1 n).image T
  have hK : plim μ T 1 (K : Set Y) = 1 := by
    rcases zero_one hμ hV hc (K : Set Y) with h | h
    · exfalso
      have hPn : Pn μ T n 1 (K : Set Y) = 1 := by
        unfold Pn
        rw [iter_congr n 1 (f' := fun _ => 1) fun y hy => by
          unfold ind; rw [if_pos (Finset.mem_coe.2 (Finset.mem_image_of_mem T hy))], iter_const hμ]
      have hstep : ∀ m, |Pn μ T (n + m) 1 (K : Set Y) - Pn μ T n 1 (K : Set Y)| ≤ tail μ T n := by
        intro m
        have := iter_diff (T := T) hμ m (K : Set Y)
        have hm := iter_abs_le hμ n (f := fun h => (Mop μ)^[m] (ind T (K : Set Y)) h -
          ind T (K : Set Y) h) (fun h => this h) 1
        rw [iter_sub, iter_sum] at hm
        simp only at hm
        have e1 : (Mop μ)^[n] ((Mop μ)^[m] (ind T (K : Set Y))) 1 = Pn μ T (n + m) 1 (K : Set Y) := by
          unfold Pn; rw [Function.iterate_add_apply]
        have e2 : ∑ i ∈ Finset.range m, (Mop μ)^[n] ((Mop μ)^[i] (Vf μ T)) 1 =
            ∑ i ∈ Finset.range m, (Mop μ)^[n + i] (Vf μ T) 1 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Function.iterate_add_apply]
        rw [e1, e2] at hm
        unfold Pn at hm ⊢
        have := sum_le_tail hμ hV n m
        linarith
      have hlim : Tendsto (fun m => Pn μ T (n + m) 1 (K : Set Y)) atTop (𝓝 0) := by
        have := (tendsto_plim hμ hV 1 (K : Set Y)).comp (tendsto_atTop_atTop_of_monotone
          (fun a b hab => by omega) fun b => ⟨b, by omega⟩ : Tendsto (fun m => n + m) atTop atTop)
        rwa [h] at this
      have : 1 - tail μ T n ≤ 0 := ge_of_tendsto' hlim fun m => by
        have := hstep m
        rw [hPn, abs_le] at this
        linarith
      linarith
    · exact h
  rw [plim_finset hμ hV] at hK
  have h01 : ∀ k, plim μ T 1 {k} = 0 ∨ plim μ T 1 {k} = 1 := fun k => zero_one hμ hV hc {k}
  have hex : ∃ k ∈ K, plim μ T 1 {k} = 1 := by
    by_contra hne
    push Not at hne
    rw [Finset.sum_eq_zero fun k hk => (h01 k).resolve_right (hne k hk)] at hK
    norm_num at hK
  obtain ⟨y0, -, hy0⟩ := hex
  refine ⟨y0, hy0, fun y hy => ?_⟩
  by_contra hne
  have := plim_finset hμ hV ({y, y0} : Finset Y) 1
  rw [Finset.sum_pair hne, hy, hy0] at this
  have := plim_le_one hμ hV 1 (({y, y0} : Finset Y) : Set Y)
  linarith

/-- No non-trivial boundary makes every `plim (·) A` constant. -/
lemma const_of_not (hnb : ¬ HasNontrivialBoundary μ) (g : G) (A : Set Y) :
    plim μ T g A = plim μ T 1 A := by
  by_contra hne
  apply hnb
  refine ⟨fun g => plim μ T g A, ⟨1, fun g => ?_⟩, fun g _ => ?_, g, 1, hne⟩
  · rw [abs_le]; constructor <;> linarith [plim_nonneg hμ hV g A, plim_le_one hμ hV g A]
  · show plim μ T g A = μ.sum fun h w => w * plim μ T (g * h) A
    rw [plim_harmonic hμ hV g A]
    rfl

end Boundary

end JMMS.IETT110

/-! # Theorem 1.10, part F: non-trivial boundary in rational rank at least 3 -/

open IntervalExchange Filter Topology

set_option linter.unusedSectionVars false

namespace JMMS.IETT110

open Classical

local notation "Cir" => UnitAddCircle

/-! ## First-step decomposition of the laws `qlaw` -/

section FirstStep

variable {G X : Type*} [Group G] [MulAction G X] {μ : G →₀ ℝ}

lemma R_lin {ι : Type*} (s : Finset ι) (c : ι → ℝ) (F : ι → X → ℝ) :
    R μ (fun z => ∑ i ∈ s, c i * F i z) = fun z => ∑ i ∈ s, c i * R μ (F i) z := by
  funext z
  unfold R
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => by ring

lemma Riter_lin {ι : Type*} (n : ℕ) (s : Finset ι) (c : ι → ℝ) (F : ι → X → ℝ) :
    (R μ)^[n] (fun z => ∑ i ∈ s, c i * F i z) = fun z => ∑ i ∈ s, c i * (R μ)^[n] (F i) z := by
  induction n generalizing F with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply]
    rw [R_lin, ih]

lemma qlaw_eq (y : X) (n : ℕ) : qlaw μ y n = (R μ)^[n] (qlaw μ y 0) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ← ih]; rfl

lemma qlaw_first (y : X) (n : ℕ) (a : X) :
    qlaw μ y (n + 1) a = ∑ s ∈ μ.support, μ s * qlaw μ (s⁻¹ • y) n a := by
  have h1 : qlaw μ y 1 = fun z => ∑ s ∈ μ.support, μ s * qlaw μ (s⁻¹ • y) 0 z := by
    funext z
    show ∑ s ∈ μ.support, μ s * (if s • z = y then 1 else 0) = _
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [qlaw]
    congr 1
    by_cases h : s • z = y
    · rw [if_pos h, if_pos]; rw [← h, inv_smul_smul]
    · rw [if_neg h, if_neg]; rintro rfl; exact h (smul_inv_smul s y)
  rw [qlaw_eq, Function.iterate_succ_apply]
  have : R μ (qlaw μ y 0) = qlaw μ y 1 := rfl
  rw [this, h1, Riter_lin]
  simp_rw [← qlaw_eq]

end FirstStep

/-! ## The walk on the group and the walk on the circle -/

section Link

variable {G X : Type*} [Group G] [MulAction G X] {μ : G →₀ ℝ}

lemma iter_hit (x a : X) (n : ℕ) (g : G) :
    (Mop μ)^[n] (fun h => if h⁻¹ • x = a then 1 else 0) g = qlaw μ (g⁻¹ • x) n a := by
  induction n generalizing g with
  | zero =>
    simp only [Function.iterate_zero, id, qlaw]
    by_cases h : g⁻¹ • x = a
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  | succ n ih =>
    rw [Function.iterate_succ_apply', qlaw_first]
    show ∑ s ∈ μ.support, μ s * (Mop μ)^[n] _ (g * s) = _
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ih, mul_inv_rev, mul_smul]

end Link

/-! ## The rank hypothesis -/

lemma exists_inj_Z3 (Λ : AddSubgroup Cir) (h : 3 ≤ rationalRank Λ) :
    ∃ ψ : (Fin 3 → ℤ) →+ Λ, Function.Injective ψ := by
  by_contra hne
  have hall : ∀ d : ℕ, (∃ f : (Fin d → ℤ) →+ Λ, Function.Injective f) → d ≤ 2 := by
    intro d ⟨f, hf⟩
    by_contra hd
    push Not at hd
    apply hne
    let e : (Fin 3 → ℤ) →+ (Fin d → ℤ) :=
      { toFun := fun v i => if hi : i.val < 3 then v ⟨i.val, hi⟩ else 0
        map_zero' := by funext i; simp
        map_add' := by intro v w; funext i; simp only [Pi.add_apply]; split_ifs <;> simp }
    refine ⟨f.comp e, hf.comp fun v w hvw => ?_⟩
    funext i
    have := congrFun hvw ⟨i.val, by omega⟩
    simpa [e] using this
  have : rationalRank Λ ≤ 2 := by
    unfold rationalRank
    refine iSup_le fun d => iSup_le fun hd => ?_
    exact_mod_cast hall d hd
  have := h.trans this
  norm_num at this

/-! ## The assembly -/

section PartII

variable (Gs : Subgroup (Equiv.Perm Cir)) (hG : Gs ≤ IET)

/-- The cocycle `τ` on `Gs`. -/
noncomputable def τG (h : Gs) : Equiv.Perm Cir := τ ⟨(h : Equiv.Perm Cir), hG h.2⟩

lemma τG_mul (g h : Gs) :
    τG Gs hG (g * h) = τG Gs hG g * ((g : Equiv.Perm Cir) * τG Gs hG h * (g : Equiv.Perm Cir)⁻¹) := by
  unfold τG
  rw [← τ_mul]
  rfl

lemma angle_mem {g : Equiv.Perm Cir} (hg : g ∈ Gs) (x : Cir) : g x - x ∈ angleGroup Gs :=
  AddSubgroup.subset_closure ⟨g, hg, x, rfl⟩

lemma smul_def' (g : Gs) (x : Cir) : g • x = (g : Equiv.Perm Cir) x := rfl

include hG in
theorem hasNontrivialBoundary_of_rank
    (hrk : 3 ≤ rationalRank (angleGroup Gs)) (hrot : ∀ a ∈ angleGroup Gs, IntervalExchange.rotation a ∈ Gs)
    (hnr : ∃ g ∈ Gs, ∀ a ∈ angleGroup Gs, g ≠ IntervalExchange.rotation a)
    (μ : Gs →₀ ℝ) (hμ : ThompsonAmenability.IsProbability μ) (hnd : IsNondegenerate μ) :
    HasNontrivialBoundary μ := by
  set Λ := angleGroup Gs
  obtain ⟨ψ, hψ⟩ := exists_inj_Z3 Λ hrk
  -- Hardy inequalities at every point of the circle
  have hH : ∀ o : Cir, ∃ C, 0 ≤ C ∧ ∀ f : Cir → ℝ, FS f → f o ^ 2 ≤ C * B μ f f := by
    intro o
    have := hardy_of_Z3 (X := Cir) hμ.1 hnd (fun z => o + ((ψ z : Λ) : Cir))
      (fun v w hvw => hψ (Subtype.ext (add_left_cancel hvw)))
      (fun v => (⟨IntervalExchange.rotation ((ψ v : Λ) : Cir), hrot _ (ψ v).2⟩ : Gs))
      (fun v z => by
        rw [smul_def']
        simp only [IntervalExchange.rotation, Equiv.coe_addRight, map_add, AddSubgroup.coe_add]
        abel)
    simpa using this
  -- the labels and their summable changes
  set T : Cir → Gs → Cir := fun x h => τG Gs hG h x
  -- the finite set of points moved by the steps
  have hfin : (⋃ s ∈ (μ.support : Set Gs), {y : Cir | τG Gs hG s y ≠ y}).Finite :=
    Set.Finite.biUnion μ.support.finite_toSet fun s _ => τ_support_finite _
  set Sig := hfin.toFinset
  have hV : ∀ x g, Summable fun n => (Mop μ)^[n] (Vf μ (T x)) g := by
    intro x g
    have hle : ∀ h : Gs, Vf μ (T x) h ≤ ∑ a ∈ Sig, if h⁻¹ • x = a then 1 else 0 := by
      intro h
      unfold Vf
      split_ifs with hc
      · obtain ⟨s, hs, hne⟩ := hc
        have hmem : h⁻¹ • x ∈ Sig := by
          rw [Set.Finite.mem_toFinset]
          refine Set.mem_biUnion (x := s) hs ?_
          intro heq
          apply hne
          simp only [T, τG_mul, Equiv.Perm.mul_apply]
          rw [show (h : Equiv.Perm Cir)⁻¹ x = h⁻¹ • x from rfl, heq]
          congr 1
          exact smul_inv_smul h x
        rw [Finset.sum_eq_single (h⁻¹ • x) (fun b _ hb => if_neg (Ne.symm hb))
          (fun hn => absurd hmem hn), if_pos rfl]
      · exact Finset.sum_nonneg fun a _ => by split_ifs <;> norm_num
    refine Summable.of_nonneg_of_le (fun n => iter_Vf_nonneg hμ n g)
      (fun n => iter_mono hμ n hle g) ?_
    have e : ∀ n, (Mop μ)^[n] (fun h : Gs => ∑ a ∈ Sig, (if h⁻¹ • x = a then (1:ℝ) else 0)) g =
        ∑ a ∈ Sig, qlaw μ (g⁻¹ • x) n a := fun n => by
      rw [iter_sum]; exact Finset.sum_congr rfl fun a _ => by convert iter_hit (μ := μ) x a n g
    simp_rw [e]
    exact summable_sum fun a _ => summable_qlaw hμ hH _ a
  -- suppose the boundary is trivial
  by_contra hnb
  have hc : ∀ x g A, plim μ (T x) g A = plim μ (T x) 1 A := fun x g A =>
    const_of_not hμ (hV x) hnb g A
  choose F hF1 hFu using fun x => exists_dirac hμ (hV x) (hc x)
  -- equivariance of the limit law
  have hshift : ∀ x (g : Gs) (A : Set Cir), plim μ (T x) g A =
      plim μ (T (g⁻¹ • x)) 1 {k | τG Gs hG g ((g : Equiv.Perm Cir) k) ∈ A} := by
    intro x g A
    have e : ∀ n, Pn μ (T x) n g A =
        Pn μ (T (g⁻¹ • x)) n 1 {k | τG Gs hG g ((g : Equiv.Perm Cir) k) ∈ A} := by
      intro n
      unfold Pn
      have := iter_left (μ := μ) n (ind (T x) A) g 1
      rw [mul_one] at this
      rw [this]
      refine congrArg (fun f => (Mop μ)^[n] f 1) (funext fun y => ?_)
      unfold ind
      simp only [T, τG_mul, Equiv.Perm.mul_apply, Set.mem_ofPred_eq]
      rfl
    exact tendsto_nhds_unique (tendsto_plim hμ (hV x) g A)
      ((tendsto_plim hμ (hV _) 1 _).congr fun n => (e n).symm)
  have hequiv : ∀ (g : Gs) y, F ((g : Equiv.Perm Cir) y) =
      τG Gs hG g ((g : Equiv.Perm Cir) (F y)) := by
    intro g y
    set x := (g : Equiv.Perm Cir) y
    have hy : g⁻¹ • x = y := by simp [x, smul_def']
    have h1 := hshift x g {F x}
    rw [hc x g, hF1 x, hy] at h1
    -- the set is the singleton of `g⁻¹ τ_g⁻¹ (F x)`
    set k0 := (g : Equiv.Perm Cir)⁻¹ ((τG Gs hG g)⁻¹ (F x))
    have hset : {k | τG Gs hG g ((g : Equiv.Perm Cir) k) ∈ ({F x} : Set Cir)} = {k0} := by
      ext k
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, k0]
      constructor
      · intro h; rw [← h]; simp
      · intro h; rw [h]; simp
    rw [hset] at h1
    have := hFu y k0 h1.symm
    rw [← this]
    simp [k0]
  -- cosets
  have hcos : ∀ x, F x - x ∈ Λ := by
    intro x
    by_contra hnot
    have h0 : ∀ n, Pn μ (T x) n 1 {F x} = 0 := by
      intro n
      unfold Pn
      have : ind (T x) {F x} = fun _ => 0 := by
        funext h
        unfold ind
        rw [if_neg]
        intro hm
        rw [Set.mem_singleton_iff] at hm
        apply hnot
        rw [← hm]
        exact τ_sub_mem Λ _ (fun z => angle_mem Gs h.2 z) x
      rw [this, iter_const hμ]
    have := tendsto_nhds_unique (tendsto_plim hμ (hV x) 1 {F x})
      (tendsto_const_nhds.congr fun n => (h0 n).symm)
    rw [hF1 x] at this
    norm_num at this
  -- IntervalExchange.rotations
  have hrotF : ∀ y, ∀ a ∈ Λ, F (y + a) = F y + a := by
    intro y a ha
    have h := hequiv ⟨IntervalExchange.rotation a, hrot a ha⟩ y
    have hτ : τG Gs hG ⟨IntervalExchange.rotation a, hrot a ha⟩ = 1 :=
      τ_eq_one_of_continuous _ (continuous_add_const a)
    rw [hτ] at h
    simpa [IntervalExchange.rotation] using h
  -- the non-IntervalExchange.rotation
  obtain ⟨g0, hg0, hg0r⟩ := hnr
  have hτ0 : τG Gs hG ⟨g0, hg0⟩ ≠ 1 := by
    intro h1
    obtain ⟨c, hc⟩ := rotation_of_τ_eq_one _ h1
    have hcΛ : c ∈ Λ := by
      have := angle_mem Gs hg0 0
      simpa [show g0 0 = 0 + c from hc 0] using this
    exact hg0r c hcΛ (Equiv.ext fun z => by simpa [IntervalExchange.rotation] using hc z)
  obtain ⟨z, hz⟩ : ∃ z, τG Gs hG ⟨g0, hg0⟩ z ≠ z := by
    by_contra hall
    push Not at hall
    exact hτ0 (Equiv.ext hall)
  set w := g0⁻¹ z
  have hw : tl g0 w ≠ g0 w := by
    have := τ_apply_smul ⟨g0, hG hg0⟩ w
    simp only at this
    rw [← this]
    have hz' : g0 w = z := by simp [w]
    rw [hz']
    exact hz
  set δ := F w - w
  have hδ : δ ∈ Λ := hcos w
  have hFv : ∀ v, v - w ∈ Λ → F v = v + δ := by
    intro v hv
    have := hrotF w (v - w) hv
    rw [show w + (v - w) = v by abel] at this
    rw [this]; simp only [δ]; abel
  -- density of the angle group
  have hdense : Dense (Λ : Set Cir) := by
    have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
    set e : Fin 3 → ℤ := Pi.single 0 1
    set c : Cir := ((ψ e : Λ) : Cir)
    have hc0 : addOrderOf c = 0 := by
      rw [addOrderOf_eq_zero_iff']
      intro n hn hnc
      have : ψ ((n : ℤ) • e) = 0 := by
        apply Subtype.ext
        rw [map_zsmul, AddSubgroup.coe_zsmul]
        simpa [c] using hnc
      have h2 := hψ (this.trans (map_zero ψ).symm)
      have := congrFun h2 0
      simp [e] at this
      omega
    have hd := (AddCircle.denseRange_zsmul_iff (a := c)).2 hc0
    refine hd.mono ?_
    rintro _ ⟨m, rfl⟩
    exact Λ.zsmul_mem (ψ e).2 m
  have key := tl_eq_of_shift (hG hg0) hdense (w - δ) δ (fun a ha => by
    set v := w - δ + a
    have hv : v - w ∈ Λ := by
      have := Λ.sub_mem ha hδ
      convert this using 1; simp only [v]; abel
    have h1 : F (g0 v) = τG Gs hG ⟨g0, hg0⟩ (g0 (F v)) := hequiv ⟨g0, hg0⟩ v
    have hgv : g0 v - w ∈ Λ := by
      have := Λ.add_mem (angle_mem Gs hg0 v) hv
      convert this using 1; abel
    have h3 : τG Gs hG ⟨g0, hg0⟩ (g0 (v + δ)) = tl g0 (v + δ) :=
      τ_apply_smul ⟨g0, hG hg0⟩ (v + δ)
    rw [hFv _ hgv, hFv v hv, h3] at h1
    rw [show w - δ + a + δ = v + δ by simp only [v]]
    exact h1.symm)
  rw [show w - δ + δ = w by abel] at key
  exact hw key

end PartII

end JMMS.IETT110

/-! # Theorem 1.10, part G1: algebraic preliminaries for rational rank 1 -/

open IntervalExchange CantorSystems

set_option linter.unusedSectionVars false

namespace JMMS.IETT110

open Classical

local notation "Cir" => UnitAddCircle

section Alg

variable (Gs : Subgroup (Equiv.Perm Cir))

lemma angleG_mem {g : Equiv.Perm Cir} (hg : g ∈ Gs) (x : Cir) : g x - x ∈ angleGroup Gs :=
  AddSubgroup.subset_closure ⟨g, hg, x, rfl⟩

/-- The angle group of a finitely generated subgroup of `IET` is finitely generated. -/
lemma angleGroup_fg (hG : Gs ≤ IET) (S : Finset (Equiv.Perm Cir))
    (hS : Subgroup.closure (S : Set (Equiv.Perm Cir)) = Gs) : (angleGroup Gs).FG := by
  have hfin : (⋃ s ∈ (S : Set (Equiv.Perm Cir)), angles s).Finite :=
    Set.Finite.biUnion S.finite_toSet fun s hs =>
      ((mem_IET_iff s).1 (hG (hS ▸ Subgroup.subset_closure hs))).2.1
  refine ⟨hfin.toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset]
  apply le_antisymm
  · refine AddSubgroup.closure_le _ |>.2 ?_
    intro a ha
    simp only [Set.mem_iUnion] at ha
    obtain ⟨s, hs, x, rfl⟩ := ha
    exact angleG_mem Gs (hS ▸ Subgroup.subset_closure hs) x
  · refine AddSubgroup.closure_le _ |>.2 ?_
    rintro a ⟨g, hg, x, rfl⟩
    set Λ0 := AddSubgroup.closure (⋃ s ∈ (S : Set (Equiv.Perm Cir)), angles s)
    rw [← hS] at hg
    induction hg using Subgroup.closure_induction generalizing x with
    | mem s hs =>
      exact AddSubgroup.subset_closure (Set.mem_biUnion hs ⟨x, rfl⟩)
    | one => simp
    | mul g h _ _ ihg ihh =>
      have := Λ0.add_mem (ihg (h x)) (ihh x)
      simpa [Equiv.Perm.mul_apply] using this
    | inv g _ ih =>
      have := Λ0.neg_mem (ih (g⁻¹ x))
      simpa using this

/-- A finitely generated subgroup of `IET` lies in some `IET(Λ; σ)`. -/
lemma le_IETOn (hG : Gs ≤ IET) (S : Finset (Equiv.Perm Cir))
    (hS : Subgroup.closure (S : Set (Equiv.Perm Cir)) = Gs) :
    ∃ σ : Finset Cir, σ.Nonempty ∧ Gs ≤ IETOn (angleGroup Gs) σ := by
  have hS' : ∀ s ∈ S, s ∈ Gs := fun s hs => hS ▸ Subgroup.subset_closure hs
  have hfin : (⋃ s ∈ (S : Set (Equiv.Perm Cir)),
      ({x | ¬ ContinuousAt s x} ∪ {x | ¬ ContinuousAt (s⁻¹ : Equiv.Perm Cir) x})).Finite :=
    Set.Finite.biUnion S.finite_toSet fun s hs =>
      (((mem_IET_iff s).1 (hG (hS' s hs))).2.2).union
        ((mem_IET_iff _).1 (hG (Gs.inv_mem (hS' s hs)))).2.2
  refine ⟨insert 0 hfin.toFinset, Finset.insert_nonempty _ _, ?_⟩
  refine (le_of_eq hS.symm).trans ((Subgroup.closure_le _).2 fun s hs => ?_)
  refine ⟨⟨hG (hS' s hs), fun x => angleG_mem Gs (hS' s hs) x⟩, fun x hx => ?_⟩
  have hxσ : x ∉ (insert 0 hfin.toFinset : Finset Cir) := fun h =>
    hx ⟨x, h, by simp⟩
  have hx' : x ∉ hfin.toFinset := fun h => hxσ (Finset.mem_insert_of_mem h)
  rw [Set.Finite.mem_toFinset] at hx'
  constructor
  · by_contra hc
    exact hx' (Set.mem_biUnion hs (Or.inl hc))
  · by_contra hc
    exact hx' (Set.mem_biUnion hs (Or.inr hc))

lemma countable_of_fg (hfg : Gs.FG) : Countable Gs := by
  have : Group.FG Gs := (Group.fg_iff_subgroup_fg Gs).2 hfg
  obtain ⟨α, hα, φ, hφ⟩ := Group.fg_iff_exists_freeGroup_hom_surjective_finite.1 this
  have : Countable (FreeGroup α) :=
    Function.Surjective.countable (f := FreeGroup.mk) (fun x => by
      induction x using Quot.induction_on with
      | h l => exact ⟨l, rfl⟩)
  exact hφ.countable

end Alg

section Rank

variable {Λ : AddSubgroup Cir}

lemma le_rationalRank {d : ℕ} (f : (Fin d → ℤ) →+ Λ) (hf : Function.Injective f) :
    (d : ℕ∞) ≤ rationalRank Λ := by
  unfold rationalRank
  exact le_iSup₂ (f := fun (d : ℕ) (_ : ∃ f : (Fin d → ℤ) →+ Λ, Function.Injective f) =>
    (d : ℕ∞)) d ⟨f, hf⟩

/-- Rational rank `1` gives an element of infinite order. -/
lemma exists_infinite_order (h : rationalRank Λ = 1) : ∃ γ : Λ, addOrderOf γ = 0 := by
  by_contra hne
  push Not at hne
  have hall : ∀ d : ℕ, (∃ f : (Fin d → ℤ) →+ Λ, Function.Injective f) → d = 0 := by
    intro d ⟨f, hf⟩
    by_contra hd
    have hd' : 0 < d := Nat.pos_of_ne_zero hd
    let e : Fin d → ℤ := Pi.single ⟨0, hd'⟩ 1
    apply hne (f e)
    rw [addOrderOf_eq_zero_iff']
    intro n hn h0
    have : f (n • e) = f 0 := by rw [map_nsmul, h0, map_zero]
    have := congrFun (hf this) ⟨0, hd'⟩
    simp [e] at this
    omega
  have : rationalRank Λ ≤ 0 := by
    unfold rationalRank
    refine iSup_le fun d => iSup_le fun hd => ?_
    rw [hall d hd]; rfl
  rw [h] at this
  norm_num at this

/-- In rational rank `1`, the multiples of an element of infinite order have finite index. -/
lemma finiteIndex_zmultiples (hfg : Λ.FG) (h : rationalRank Λ = 1) (γ : Λ)
    (hγ : addOrderOf γ = 0) : (AddSubgroup.zmultiples γ).FiniteIndex := by
  have hFG : AddGroup.FG Λ := (AddGroup.fg_iff_addSubgroup_fg Λ).2 hfg
  set Z := AddSubgroup.zmultiples γ
  have hFGq : AddGroup.FG (Λ ⧸ Z) := inferInstance
  have htors : ∀ q : Λ ⧸ Z, IsOfFinAddOrder q := by
    intro q
    obtain ⟨l, rfl⟩ := QuotientAddGroup.mk_surjective q
    -- some nonzero multiple of `l` lies in `⟨γ⟩`
    by_contra hinf
    let F : (Fin 2 → ℤ) →+ Λ :=
      { toFun := fun v => v 0 • γ + v 1 • l
        map_zero' := by simp
        map_add' := by intro v w; simp only [Pi.add_apply, add_zsmul]; abel }
    have hF : Function.Injective F := by
      rw [injective_iff_map_eq_zero]
      intro v hv
      simp only [F, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hv
      have hv1 : v 1 = 0 := by
        by_contra h1
        apply hinf
        refine isOfFinAddOrder_iff_zsmul_eq_zero.2 ⟨v 1, h1, ?_⟩
        rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff]
        have : v 1 • l = -(v 0 • γ) := eq_neg_of_add_eq_zero_right hv
        rw [this]
        exact Z.neg_mem (AddSubgroup.zsmul_mem_zmultiples _ _)
      have hv0 : v 0 = 0 := by
        rw [hv1, zero_zsmul, add_zero] at hv
        by_contra h0
        have : IsOfFinAddOrder γ := isOfFinAddOrder_iff_zsmul_eq_zero.2 ⟨v 0, h0, hv⟩
        exact (addOrderOf_eq_zero_iff.1 hγ) this
      funext i
      fin_cases i
      · exact hv0
      · exact hv1
    have := le_rationalRank F hF
    rw [h] at this
    norm_num at this
  have : Finite (Λ ⧸ Z) := by
    have h1 : Module.Finite ℤ (Λ ⧸ Z) := Module.Finite.iff_addGroup_fg.2 hFGq
    exact Module.finite_of_fg_torsion _ ((isAddTorsion_iff_isTorsion_int).1 htors)
  exact AddSubgroup.finiteIndex_of_finite_quotient

end Rank

end JMMS.IETT110

/-! # Theorem 1.10, part G2: dividing a subshift by the kernel of its action

For a minimal subshift `S ⊆ A^Λ`, the subgroup `K` of shifts acting trivially is also the
stabiliser of every point. The descended subshift `S' ⊆ A^(Λ/K)` is homeomorphic to `S`,
equivariantly, so `[[Λ]]` on `S` embeds in `[[Λ/K]]` on `S'`; the action on `S'` is free, and the
complexity does not grow. -/

open CantorSystems Topology

set_option linter.unusedSectionVars false

namespace JMMS.IETT110

open Classical

section Quot

variable {Λ A : Type*} [AddCommGroup Λ] [TopologicalSpace A] [DiscreteTopology A]
variable (S : Subshift Λ A)

/-- The shifts acting trivially on `S`. -/
def kerS : AddSubgroup Λ where
  carrier := {κ | ∀ x : S, κ +ᵥ x = x}
  zero_mem' := fun x => zero_vadd _ x
  add_mem' := by
    intro a b ha hb x
    rw [add_vadd, hb, ha]
  neg_mem' := by
    intro a ha x
    have := ha (-a +ᵥ x)
    rw [vadd_neg_vadd] at this
    exact this.symm

variable {S}

lemma kerS_apply {κ : Λ} (hκ : κ ∈ kerS S) (x : S) (δ : Λ) : x.1 (δ + κ) = x.1 δ := by
  have := congrArg (fun z : S => z.1 δ) (hκ x)
  simpa [Subshift.coe_vadd] using this

lemma apply_eq_of_mk_eq (x : S) {δ δ' : Λ}
    (h : (δ : Λ ⧸ kerS S) = (δ' : Λ ⧸ kerS S)) : x.1 δ' = x.1 δ := by
  rw [QuotientAddGroup.eq] at h
  have := kerS_apply h x δ
  rw [add_neg_cancel_left] at this
  exact this

variable (S)

/-- The descended subshift on `Λ ⧸ K`. -/
def qS : Subshift (Λ ⧸ kerS S) A where
  carrier := {y | (fun δ : Λ => y (δ : Λ ⧸ kerS S)) ∈ S}
  isSubshift := by
    constructor
    · have hc : Continuous fun y : Λ ⧸ kerS S → A => fun δ : Λ => y (δ : Λ ⧸ kerS S) :=
        continuous_pi fun δ => continuous_apply _
      exact S.isSubshift.1.preimage hc
    · intro γ' y hy
      obtain ⟨γ, rfl⟩ := QuotientAddGroup.mk_surjective γ'
      have := S.isSubshift.2 γ _ hy
      exact this

/-- `Φ : S' → S`. -/
def Φ (y : qS S) : S := ⟨fun δ => y.1 (δ : Λ ⧸ kerS S), y.2⟩

/-- `Ψ : S → S'`. -/
noncomputable def Ψ (x : S) : qS S :=
  ⟨fun γ => x.1 γ.out, by
    show (fun δ : Λ => x.1 (δ : Λ ⧸ kerS S).out) ∈ S
    convert x.2 using 1
    funext δ
    exact apply_eq_of_mk_eq x (by simp)⟩

lemma Φ_Ψ (x : S) : Φ S (Ψ S x) = x := by
  apply Subtype.ext
  funext δ
  exact apply_eq_of_mk_eq x (by simp)

lemma Ψ_Φ (y : qS S) : Ψ S (Φ S y) = y := by
  apply Subtype.ext
  funext γ
  show y.1 ((γ.out : Λ) : Λ ⧸ kerS S) = y.1 γ
  rw [QuotientAddGroup.out_eq']

lemma Φ_cont : Continuous (Φ S) := by
  unfold Φ
  apply Continuous.subtype_mk
  exact continuous_pi fun δ => (continuous_apply _).comp continuous_subtype_val

lemma Ψ_cont : Continuous (Ψ S) := by
  unfold Ψ
  apply Continuous.subtype_mk
  exact continuous_pi fun γ => (continuous_apply _).comp continuous_subtype_val

/-- `Φ` as a homeomorphism. -/
noncomputable def Φh : qS S ≃ₜ S where
  toFun := Φ S
  invFun := Ψ S
  left_inv := Ψ_Φ S
  right_inv := Φ_Ψ S
  continuous_toFun := Φ_cont S
  continuous_invFun := Ψ_cont S

lemma Φ_vadd (γ : Λ) (y : qS S) : Φ S ((γ : Λ ⧸ kerS S) +ᵥ y) = γ +ᵥ Φ S y := by
  apply Subtype.ext
  funext δ
  rfl

lemma Ψ_vadd (γ : Λ) (x : S) : Ψ S (γ +ᵥ x) = (γ : Λ ⧸ kerS S) +ᵥ Ψ S x := by
  rw [← Φ_Ψ S x, ← Φ_vadd, Ψ_Φ, Ψ_Φ]

/-- Conjugation by `Φ` maps `[[Λ]]` into `[[Λ/K]]`. -/
noncomputable def conjHom : topologicalFullGroup Λ S →* topologicalFullGroup (Λ ⧸ kerS S) (qS S) where
  toFun f := ⟨(Φh S).trans ((f : S ≃ₜ S).trans (Φh S).symm), by
    intro y
    obtain ⟨U, hU, γ, hγ⟩ := f.2 (Φ S y)
    refine ⟨Φ S ⁻¹' U, (Φ_cont S).continuousAt.preimage_mem_nhds hU, (γ : Λ ⧸ kerS S), ?_⟩
    intro z hz
    show Ψ S ((f : S ≃ₜ S) (Φ S z)) = _
    rw [hγ _ hz, Ψ_vadd, Ψ_Φ]⟩
  map_one' := by
    apply Subtype.ext
    apply Homeomorph.ext
    intro y
    show Ψ S (Φ S y) = y
    exact Ψ_Φ S y
  map_mul' f g := by
    apply Subtype.ext
    apply Homeomorph.ext
    intro y
    show Ψ S ((f : S ≃ₜ S) ((g : S ≃ₜ S) (Φ S y))) =
      Ψ S ((f : S ≃ₜ S) (Φ S (Ψ S ((g : S ≃ₜ S) (Φ S y)))))
    rw [Φ_Ψ]

lemma conjHom_injective : Function.Injective (conjHom S) := by
  intro f g h
  apply Subtype.ext
  apply Homeomorph.ext
  intro x
  have := congrArg (fun k : topologicalFullGroup (Λ ⧸ kerS S) (qS S) => (k : qS S ≃ₜ qS S) (Ψ S x)) h
  change Ψ S ((f : S ≃ₜ S) (Φ S (Ψ S x))) = Ψ S ((g : S ≃ₜ S) (Φ S (Ψ S x))) at this
  rw [Φ_Ψ] at this
  have := congrArg (Φ S) this
  rwa [Φ_Ψ, Φ_Ψ] at this

/-! ## Minimality: the kernel is every stabiliser -/

lemma vadd_cont (γ : Λ) : Continuous fun x : S => γ +ᵥ x := by
  show Continuous fun x : S => (⟨shift γ x.1, S.isSubshift.2 γ _ x.2⟩ : S)
  apply Continuous.subtype_mk
  exact continuous_pi fun δ => (continuous_apply _).comp continuous_subtype_val

lemma mem_kerS_of_fix [AddAction.IsMinimal Λ S] {x0 : S} {γ : Λ} (h : γ +ᵥ x0 = x0) :
    γ ∈ kerS S := by
  have hcl : IsClosed {x : S | γ +ᵥ x = x} := isClosed_eq (vadd_cont S γ) continuous_id
  have horb : AddAction.orbit Λ x0 ⊆ {x : S | γ +ᵥ x = x} := by
    rintro _ ⟨l, rfl⟩
    show γ +ᵥ (l +ᵥ x0) = l +ᵥ x0
    rw [← add_vadd, add_comm, add_vadd, h]
  have hd := AddAction.dense_orbit Λ x0
  intro x
  have := hcl.closure_subset_iff.2 horb
  rw [hd.closure_eq] at this
  exact this (Set.mem_univ x)

lemma qS_free [AddAction.IsMinimal Λ S] :
    Dense {y : qS S | ∀ γ' : Λ ⧸ kerS S, γ' +ᵥ y = y → γ' = 0} := by
  convert dense_univ
  ext y
  simp only [Set.mem_univ, iff_true]
  intro γ' hγ'
  obtain ⟨γ, rfl⟩ := QuotientAddGroup.mk_surjective γ'
  have : γ +ᵥ Φ S y = Φ S y := by rw [← Φ_vadd, hγ']
  rw [QuotientAddGroup.eq_zero_iff]
  exact mem_kerS_of_fix S this

/-- In a minimal Cantor subshift, a finite-index subgroup does not act trivially. -/
lemma not_le_kerS_of_finiteIndex [AddAction.IsMinimal Λ S] (hC : IsCantorSpace S)
    (H : AddSubgroup Λ) [H.FiniteIndex] (hH : H ≤ kerS S) : False := by
  obtain ⟨x0⟩ := hC.1
  -- the orbit of `x0` is finite
  have hfin : (AddAction.orbit Λ x0).Finite := by
    have : AddAction.orbit Λ x0 ⊆
        Set.range fun q : Λ ⧸ H => (q.out : Λ) +ᵥ x0 := by
      rintro _ ⟨l, rfl⟩
      refine ⟨(l : Λ ⧸ H), ?_⟩
      show ((l : Λ ⧸ H).out : Λ) +ᵥ x0 = l +ᵥ x0
      have hq : -((l : Λ ⧸ H).out) + l ∈ H := by
        rw [← QuotientAddGroup.eq]; simp
      have := hH hq x0
      calc ((l : Λ ⧸ H).out : Λ) +ᵥ x0 = ((l : Λ ⧸ H).out : Λ) +ᵥ
            ((-((l : Λ ⧸ H).out) + l) +ᵥ x0) := by rw [this]
        _ = l +ᵥ x0 := by rw [← add_vadd, add_neg_cancel_left]
    exact (Set.finite_range _).subset this
  have hclo : IsClosed (AddAction.orbit Λ x0) := hfin.isClosed
  have huniv : AddAction.orbit Λ x0 = Set.univ := by
    rw [← hclo.closure_eq, (AddAction.dense_orbit Λ x0).closure_eq]
  have hfS : (Set.univ : Set S).Finite := huniv ▸ hfin
  apply hC.2.2.2.2 x0
  have : ({x0} : Set S) = ((Set.univ : Set S) \ {x0})ᶜ := by ext; simp
  rw [this]
  exact ((hfS.subset Set.sdiff_subset).isClosed).isOpen_compl

/-- The image of an element whose nonzero multiples have finite index has infinite order and
finite-index multiples in `Λ ⧸ K`. -/
lemma virtuallyCyclic_quot [AddAction.IsMinimal Λ S] (hC : IsCantorSpace S) (γ0 : Λ)
    (hzm : ∀ m : ℤ, m ≠ 0 → (AddSubgroup.zmultiples (m • γ0)).FiniteIndex) :
    ∃ γ : Λ ⧸ kerS S, addOrderOf γ = 0 ∧ (AddSubgroup.zmultiples γ).FiniteIndex := by
  refine ⟨(γ0 : Λ ⧸ kerS S), ?_, ?_⟩
  · rw [addOrderOf_eq_zero_iff']
    intro n hn h0
    have hm : ((n : ℤ) • γ0) ∈ kerS S := by
      rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_zsmul]
      simpa using h0
    have := hzm n (by exact_mod_cast hn.ne')
    exact not_le_kerS_of_finiteIndex S hC _ (fun z hz => by
      obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hz
      exact (kerS S).zsmul_mem hm k)
  · have h1 := hzm 1 one_ne_zero
    rw [one_zsmul] at h1
    have : Finite ((Λ ⧸ kerS S) ⧸ AddSubgroup.zmultiples (γ0 : Λ ⧸ kerS S)) := by
      have hmap : AddSubgroup.zmultiples γ0 ≤ (AddSubgroup.zmultiples (γ0 : Λ ⧸ kerS S)).comap
          (QuotientAddGroup.mk' (kerS S)) := by
        intro z hz
        obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hz
        simp only [AddSubgroup.mem_comap, map_zsmul]
        exact AddSubgroup.zsmul_mem_zmultiples _ _
      refine Finite.of_surjective (QuotientAddGroup.map _ _ (QuotientAddGroup.mk' (kerS S)) hmap) ?_
      intro q
      obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective q
      obtain ⟨l, rfl⟩ := QuotientAddGroup.mk_surjective q
      exact ⟨(l : Λ ⧸ AddSubgroup.zmultiples γ0), rfl⟩
    exact AddSubgroup.finiteIndex_of_finite_quotient

/-! ## Partitions and complexity -/

/-- The letter at `0`. -/
def p0 {Γ : Type*} [AddGroup Γ] (T : Subshift Γ A) (x : T) : A := x.1 0

lemma p0_clopen {Γ : Type*} [AddGroup Γ] (T : Subshift Γ A) : IsClopenPartition (p0 T) := by
  intro i
  exact (isClopen_discrete {i}).preimage
    ((continuous_apply 0).comp continuous_subtype_val)

lemma p0_sep {Γ : Type*} [AddGroup Γ] (T : Subshift Γ A) : IsSeparatingPartition Γ (p0 T) := by
  intro x y h
  apply Subtype.ext
  funext γ
  have := h γ
  simpa [p0, Subshift.coe_vadd] using this

lemma wordBall_finite {Γ : Type*} [AddGroup Γ] {T : Set Γ} (hT : T.Finite) (n : ℕ) :
    (wordBall T n).Finite := by
  have hT' : (T ∪ -T).Finite := hT.union hT.neg
  have : Finite ↥(T ∪ -T) := hT'.to_subtype
  refine ((List.finite_length_le ↥(T ∪ -T) n).image
    (fun l => (l.map Subtype.val).sum)).subset ?_
  rintro γ ⟨l, hl, hmem, rfl⟩
  refine ⟨l.pmap Subtype.mk (fun t ht => ?_), ?_, ?_⟩
  · rcases hmem t ht with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa using h)
  · simpa using hl
  · simp [List.map_pmap]

lemma wordBall_lift {T : Set Λ} {n : ℕ} {γ' : Λ ⧸ kerS S}
    (h : γ' ∈ wordBall ((QuotientAddGroup.mk : Λ → Λ ⧸ kerS S) '' T) n) :
    ∃ γ ∈ wordBall T n, (γ : Λ ⧸ kerS S) = γ' := by
  obtain ⟨l, hl, hmem, rfl⟩ := h
  induction l generalizing n with
  | nil => exact ⟨0, ⟨[], by simp, by simp, by simp⟩, by simp⟩
  | cons t' l ih =>
    have hl' : l.length ≤ n - 1 := by simp at hl; omega
    obtain ⟨γ, ⟨m, hm1, hm2, rfl⟩, hγ⟩ := ih hl' (fun t ht => hmem t (List.mem_cons_of_mem _ ht))
    obtain ⟨t, ht, hmk⟩ : ∃ t, (t ∈ T ∨ -t ∈ T) ∧ (t : Λ ⧸ kerS S) = t' := by
      rcases hmem t' (List.mem_cons_self) with ⟨t, ht, e⟩ | ⟨t, ht, e⟩
      · exact ⟨t, Or.inl ht, e⟩
      · exact ⟨-t, Or.inr (by simpa using ht), by rw [QuotientAddGroup.mk_neg, e, neg_neg]⟩
    refine ⟨t + m.sum, ⟨t :: m, by simp at hl ⊢; omega, ?_, by simp⟩, ?_⟩
    · intro s hs
      rcases List.mem_cons.1 hs with rfl | hs
      · exact ht
      · exact hm2 s hs
    · rw [QuotientAddGroup.mk_add, hmk, hγ, List.sum_cons]

lemma complexity_qS_le [Finite A] {T : Set Λ} (hT : T.Finite) (n : ℕ) :
    complexity ((QuotientAddGroup.mk : Λ → Λ ⧸ kerS S) '' T) (p0 (qS S)) n ≤
      complexity T (p0 S) n := by
  unfold complexity
  set R := Set.range fun x : S => fun γ : wordBall T n => p0 S (-(γ : Λ) +ᵥ x)
  set R' := Set.range fun y : qS S =>
    fun γ : wordBall ((QuotientAddGroup.mk : Λ → Λ ⧸ kerS S) '' T) n =>
      p0 (qS S) (-(γ : Λ ⧸ kerS S) +ᵥ y)
  have hmk : ∀ γ ∈ wordBall T n,
      (γ : Λ ⧸ kerS S) ∈ wordBall ((QuotientAddGroup.mk : Λ → Λ ⧸ kerS S) '' T) n := by
    rintro γ ⟨l, hl, hmem, rfl⟩
    refine ⟨l.map (QuotientAddGroup.mk), by simpa using hl, ?_, ?_⟩
    · intro t' ht'
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ht'
      rcases hmem t ht with h | h
      · exact Or.inl ⟨t, h, rfl⟩
      · exact Or.inr ⟨-t, h, by simp⟩
    · exact (map_list_sum (QuotientAddGroup.mk' (kerS S)) l).symm
  have : Finite (wordBall T n) := (wordBall_finite hT n).to_subtype
  have hRfin : Finite R := Subtype.finite
  let F : R' → R := fun P => ⟨fun γ => P.1 ⟨(γ : Λ ⧸ kerS S), hmk γ γ.2⟩, by
    obtain ⟨y, hy⟩ := P.2
    refine ⟨Φ S y, ?_⟩
    funext γ
    rw [← hy]
    rfl⟩
  have hF : Function.Injective F := by
    rintro ⟨P1, y1, rfl⟩ ⟨P2, y2, rfl⟩ h
    apply Subtype.ext
    funext γ'
    obtain ⟨γ, hγ, e⟩ := wordBall_lift (S := S) γ'.2
    have := congrFun (congrArg Subtype.val h) ⟨γ, hγ⟩
    simp only [F] at this
    show p0 (qS S) (-(γ' : Λ ⧸ kerS S) +ᵥ y1) = p0 (qS S) (-(γ' : Λ ⧸ kerS S) +ᵥ y2)
    rw [← e]
    exact this
  exact Nat.card_le_card_of_injective F hF

end Quot

end JMMS.IETT110

/-! # Theorem 1.10, part G3: entropy along injective homomorphisms, and Liouville -/

open IntervalExchange

set_option linter.unusedSectionVars false

namespace JMMS.IETT110

open Classical

section Push

variable {H Γ : Type*} [Group H] [Group Γ] (ι : H →* Γ) (hι : Function.Injective ι)
include hι

lemma extend_ι_apply (f : H → ℝ) (g : H) : Function.extend ι f 0 (ι g) = f g :=
  hι.extend_apply f 0 g

lemma extend_ι_out (f : H → ℝ) {z : Γ} (hz : z ∉ Set.range ι) : Function.extend ι f 0 z = 0 := by
  rw [Function.extend_apply']
  · rfl
  · rintro ⟨a, rfl⟩; exact hz ⟨a, rfl⟩

lemma extend_symm (f : H → ℝ) (hf : ∀ g, f g⁻¹ = f g) (z : Γ) :
    Function.extend ι f 0 z⁻¹ = Function.extend ι f 0 z := by
  by_cases hr : z ∈ Set.range ι
  · obtain ⟨g, rfl⟩ := hr
    rw [← map_inv, extend_ι_apply ι hι, extend_ι_apply ι hι]
    exact hf g
  · have hr' : z⁻¹ ∉ Set.range ι := by
      rintro ⟨g, hg⟩
      exact hr ⟨g⁻¹, by rw [map_inv, hg, inv_inv]⟩
    rw [extend_ι_out ι hι _ hr, extend_ι_out ι hι _ hr']

lemma extend_nonneg (f : H → ℝ) (hf : ∀ g, 0 ≤ f g) (z : Γ) : 0 ≤ Function.extend ι f 0 z := by
  by_cases hr : z ∈ Set.range ι
  · obtain ⟨g, rfl⟩ := hr
    rw [extend_ι_apply ι hι]; exact hf g
  · rw [extend_ι_out ι hι _ hr]

lemma extend_support_finite (f : H → ℝ) (hf : (Function.support f).Finite) :
    (Function.support (Function.extend ι f 0)).Finite := by
  refine (hf.image ι).subset ?_
  intro z hz
  by_cases hr : z ∈ Set.range ι
  · obtain ⟨g, rfl⟩ := hr
    refine ⟨g, ?_, rfl⟩
    rw [Function.mem_support, extend_ι_apply ι hι] at hz
    exact hz
  · exact absurd (extend_ι_out ι hι _ hr) hz

lemma conv_extend (f m : H → ℝ) :
    ErschlerZheng.conv (Function.extend ι f 0) (Function.extend ι m 0) =
      Function.extend ι (ErschlerZheng.conv f m) 0 := by
  funext z
  unfold ErschlerZheng.conv
  by_cases hz : z ∈ Set.range ι
  · obtain ⟨g, rfl⟩ := hz
    rw [extend_ι_apply ι hι]
    rw [← hι.tsum_eq (f := fun h => Function.extend ι f 0 h * Function.extend ι m 0 (h⁻¹ * ι g))]
    · refine tsum_congr fun g' => ?_
      rw [extend_ι_apply ι hι, ← map_inv, ← map_mul, extend_ι_apply ι hι]
    · intro h hh
      by_contra hr
      exact hh (by simp only; rw [extend_ι_out ι hι f hr, zero_mul])
  · rw [extend_ι_out ι hι _ hz]
    refine (tsum_congr fun h => ?_).trans tsum_zero
    by_cases hh : h ∈ Set.range ι
    · obtain ⟨g', rfl⟩ := hh
      rw [extend_ι_out ι hι m, mul_zero]
      rintro ⟨g'', hg''⟩
      apply hz
      refine ⟨g' * g'', ?_⟩
      rw [map_mul, hg'', mul_inv_cancel_left]
    · rw [extend_ι_out ι hι f hh, zero_mul]

lemma convPow_extend (f : H → ℝ) (n : ℕ) :
    ErschlerZheng.convPow (Function.extend ι f 0) n =
      Function.extend ι (ErschlerZheng.convPow f n) 0 := by
  induction n with
  | zero =>
    funext z
    simp only [ErschlerZheng.convPow]
    by_cases hz : z ∈ Set.range ι
    · obtain ⟨g, rfl⟩ := hz
      rw [extend_ι_apply ι hι]
      have : ι g = 1 ↔ g = 1 := by
        constructor
        · intro h; exact hι (h.trans (map_one ι).symm)
        · rintro rfl; exact map_one ι
      by_cases hg : g = 1
      · rw [if_pos (this.2 hg), if_pos hg]
      · rw [if_neg (fun h => hg (this.1 h)), if_neg hg]
    · rw [extend_ι_out ι hι _ hz, if_neg]
      rintro rfl; exact hz ⟨1, map_one ι⟩
  | succ n ih =>
    simp only [ErschlerZheng.convPow]
    rw [ih, conv_extend ι hι]

lemma entropy_extend (f : H → ℝ) :
    ErschlerZheng.entropy (Function.extend ι f 0) = ErschlerZheng.entropy f := by
  unfold ErschlerZheng.entropy
  rw [← hι.tsum_eq (f := fun z => Real.negMulLog (Function.extend ι f 0 z))]
  · exact tsum_congr fun g => by rw [extend_ι_apply ι hι]
  · intro z hz
    by_contra hr
    exact hz (by simp only; rw [extend_ι_out ι hι f hr, Real.negMulLog_zero])

lemma asymptoticEntropy_extend (f : H → ℝ) :
    ErschlerZheng.asymptoticEntropy (Function.extend ι f 0) = ErschlerZheng.asymptoticEntropy f := by
  unfold ErschlerZheng.asymptoticEntropy
  simp_rw [convPow_extend ι hι, entropy_extend ι hι]

end Push

/-! ## From the Erschler–Zheng boundary to the Liouville property -/

section Liouville

variable {H : Type*} [Group H]

lemma inv_mem_sg {μ : H →₀ ℝ} (hs : IsSymmetric μ) {x : H}
    (hx : x ∈ Subsemigroup.closure (μ.support : Set H)) :
    x⁻¹ ∈ Subsemigroup.closure (μ.support : Set H) := by
  induction hx using Subsemigroup.closure_induction with
  | mem y hy =>
    apply Subsemigroup.subset_closure
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hs]
    exact Finsupp.mem_support_iff.1 hy
  | mul a b _ _ ha hb =>
    rw [mul_inv_rev]; exact Subsemigroup.mul_mem _ hb ha

theorem isLiouville_of_not (μ : H →₀ ℝ) (hμ : ThompsonAmenability.IsProbability μ)
    (hs : IsSymmetric μ) (hnot : ¬ ErschlerZheng.HasNontrivialPoissonBoundary (μ : H → ℝ)) :
    ThompsonAmenability.IsLiouville μ := by
  set Sg := Subsemigroup.closure (μ.support : Set H)
  set Hg := Subgroup.closure (μ.support : Set H)
  have hsum : ∑ s ∈ μ.support, μ s = 1 := by simpa [Finsupp.sum] using hμ.2
  obtain ⟨s0, hs0⟩ : μ.support.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne] at hsum
    simp at hsum
  have hHS : ∀ x ∈ Hg, x ∈ Sg := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact Subsemigroup.subset_closure hy
    | one =>
      have h1 : s0 ∈ Sg := Subsemigroup.subset_closure hs0
      have := Subsemigroup.mul_mem _ h1 (inv_mem_sg hs h1)
      rwa [mul_inv_cancel] at this
    | mul a b _ _ ha hb => exact Subsemigroup.mul_mem _ ha hb
    | inv a _ ha => exact inv_mem_sg hs ha
  have hSH : ∀ x ∈ Sg, x ∈ Hg := by
    intro x hx
    induction hx using Subsemigroup.closure_induction with
    | mem y hy => exact Subgroup.subset_closure hy
    | mul a b _ _ ha hb => exact Hg.mul_mem ha hb
  have hSM : ∀ x ∈ Sg, x ∈ Submonoid.closure (Function.support (μ : H → ℝ)) := by
    intro x hx
    induction hx using Subsemigroup.closure_induction with
    | mem y hy =>
      apply Submonoid.subset_closure
      rw [Finsupp.fun_support_eq]; exact hy
    | mul a b _ _ ha hb => exact Submonoid.mul_mem _ ha hb
  intro f ⟨C, hC⟩ hharm g hg h hh
  let r : H → H := fun z => (QuotientGroup.mk z : H ⧸ Hg).out
  have hr : ∀ z, (r z)⁻¹ * z ∈ Hg := fun z => by
    rw [← QuotientGroup.eq]; exact QuotientGroup.out_eq' _
  have hr_mul : ∀ z s, s ∈ Hg → r (z * s) = r z := by
    intro z s hs'
    simp only [r]
    congr 1
    rw [QuotientGroup.eq]
    simpa using hs'
  let f' : H → ℝ := fun z => f ((r z)⁻¹ * z)
  have hbd : ∃ C, ∀ x, |f' x| ≤ C := ⟨C, fun x => hC _ (hHS _ (hr x))⟩
  have hharm' : ErschlerZheng.IsHarmonic (μ : H → ℝ) f' := by
    intro z
    rw [tsum_eq_sum (s := μ.support) (fun y hy => by
      rw [Finsupp.notMem_support_iff.1 hy, mul_zero])]
    have := hharm _ (hHS _ (hr z))
    simp only [f']
    rw [this, Finsupp.sum]
    refine Finset.sum_congr rfl fun s hs' => ?_
    rw [hr_mul z s (Subgroup.subset_closure hs'), mul_assoc, mul_comm]
  have hconst : ∀ x ∈ Submonoid.closure (Function.support (μ : H → ℝ)),
      ∀ y ∈ Submonoid.closure (Function.support (μ : H → ℝ)), f' x = f' y := by
    intro x hx y hy
    by_contra hne
    exact hnot ⟨f', hbd, hharm', x, hx, y, hy, hne⟩
  set r0 := r 1
  have hr0 : r0 ∈ Hg := by
    have := Hg.inv_mem (hr 1)
    simpa using this
  have key : ∀ x ∈ Sg, f' (r0 * x) = f x := by
    intro x hx
    simp only [f']
    have : r (r0 * x) = r0 := by
      have := hr_mul 1 (r0 * x) (Hg.mul_mem hr0 (hSH x hx))
      simpa using this
    rw [this, inv_mul_cancel_left]
  rw [← key g hg, ← key h hh]
  exact hconst _ (hSM _ (hHS _ (Hg.mul_mem hr0 (hSH g hg))))
    _ (hSM _ (hHS _ (Hg.mul_mem hr0 (hSH h hh))))

end Liouville

end JMMS.IETT110

/-! # Theorem 1.10: assembly -/

open IntervalExchange CantorSystems

set_option linter.unusedSectionVars false

namespace JMMS.IETT110

open Classical

local notation "Cir" => UnitAddCircle

theorem isLiouville_of_rank_one (Gs : Subgroup (Equiv.Perm Cir)) (hG : Gs ≤ IET) (hfg : Gs.FG)
    (h1 : rationalRank (angleGroup Gs) = 1) (μ : Gs →₀ ℝ)
    (hμ : ThompsonAmenability.IsProbability μ) (hs : IsSymmetric μ) :
    ThompsonAmenability.IsLiouville μ := by
  set Λ := angleGroup Gs
  obtain ⟨S0, hS0⟩ := hfg
  have hΛfg : Λ.FG := angleGroup_fg Gs hG S0 hS0
  obtain ⟨σ, hσ, hle⟩ := le_IETOn Gs hG S0 hS0
  obtain ⟨γ, hγ⟩ := exists_infinite_order h1
  have hinf : (Λ : Set Cir).Infinite := by
    intro hfin
    have : Finite Λ := hfin.to_subtype
    exact (addOrderOf_eq_zero_iff.1 hγ) (isOfFinAddOrder_of_finite γ)
  obtain ⟨k, S, hC, hmin, ⟨π, -, -⟩, hcx⟩ :=
    exists_isMinimal_subshift_mulEquiv_IETOn_and_complexity_le Λ hinf hΛfg σ hσ
  have hzm : ∀ m : ℤ, m ≠ 0 → (AddSubgroup.zmultiples (m • γ)).FiniteIndex := by
    intro m hm
    refine finiteIndex_zmultiples hΛfg h1 _ ?_
    rw [addOrderOf_eq_zero_iff']
    intro n hn h0
    apply addOrderOf_eq_zero_iff.1 hγ
    refine isOfFinAddOrder_iff_zsmul_eq_zero.2 ⟨(n : ℤ) * m, ?_, ?_⟩
    · exact mul_ne_zero (by exact_mod_cast hn.ne') hm
    · rw [mul_zsmul, natCast_zsmul, h0]
  obtain ⟨γ', hγ'o, hγ'fi⟩ := virtuallyCyclic_quot S hC γ hzm
  -- a finite generating set of `Λ`
  have hFG : AddGroup.FG Λ := (AddGroup.fg_iff_addSubgroup_fg Λ).2 hΛfg
  obtain ⟨T, hT⟩ := (AddGroup.fg_def.1 hFG)
  obtain ⟨C, -, hCx⟩ := hcx 1 (by rw [h1]; rfl) T hT k (p0 S) (p0_clopen S) (p0_sep S)
  set T' : Finset (Λ ⧸ kerS S) := T.image (QuotientAddGroup.mk)
  have hT' : AddSubgroup.closure (T' : Set (Λ ⧸ kerS S)) = ⊤ := by
    have e := AddMonoidHom.map_closure (QuotientAddGroup.mk' (kerS S)) (T : Set Λ)
    rw [hT, AddSubgroup.map_top_of_surjective _ (QuotientAddGroup.mk'_surjective _)] at e
    rw [Finset.coe_image]
    exact e.symm
  have hρ : ∀ n : ℕ, 1 ≤ n →
      (complexity (T' : Set (Λ ⧸ kerS S)) (p0 (qS S)) n : ℝ) ≤ C * (n : ℝ) ^ (1 : ℝ) := by
    intro n hn
    have e1 := complexity_qS_le (S := S) (T := (T : Set Λ)) T.finite_toSet n
    have e2 := hCx n hn
    rw [Real.rpow_one]
    rw [pow_one] at e2
    have : (T' : Set (Λ ⧸ kerS S)) = (QuotientAddGroup.mk : Λ → Λ ⧸ kerS S) '' (T : Set Λ) :=
      Finset.coe_image
    rw [this]
    calc ((complexity ((QuotientAddGroup.mk : Λ → Λ ⧸ kerS S) '' (T : Set Λ)) (p0 (qS S)) n : ℕ) : ℝ)
        ≤ (complexity (T : Set Λ) (p0 S) n : ℝ) := by exact_mod_cast e1
      _ ≤ C * n := e2
  -- the embedding of `Gs` in the full group
  obtain ⟨ι, hι⟩ : ∃ ι : Gs →* topologicalFullGroup (Λ ⧸ kerS S) (qS S), Function.Injective ι :=
    ⟨(conjHom S).comp (π.symm.toMonoidHom.comp (Subgroup.inclusion hle)),
      (conjHom_injective S).comp (π.symm.injective.comp (Subgroup.inclusion_injective hle))⟩
  have hsum : ∑ s ∈ μ.support, μ s = 1 := by simpa [Finsupp.sum] using hμ.2
  have hμh : HasSum (μ : Gs → ℝ) 1 := by
    rw [← hsum]
    exact hasSum_sum_of_ne_finset_zero fun g hg => Finsupp.notMem_support_iff.1 hg
  have hfin' : (Function.support (Function.extend ι (μ : Gs → ℝ) 0)).Finite :=
    extend_support_finite ι hι _ ((μ.support.finite_toSet).subset (by
      intro g hg; exact Finsupp.mem_support_iff.2 hg))
  have hprob' : ErschlerZheng.IsProbability (Function.extend ι (μ : Gs → ℝ) 0) :=
    ⟨extend_nonneg ι hι _ hμ.1, (hasSum_extend_zero hι).2 hμh⟩
  have hsymm' : ErschlerZheng.IsSymmetric (Function.extend ι (μ : Gs → ℝ) 0) :=
    extend_symm ι hι _ hs
  have : AddAction.IsMinimal Λ S := hmin
  have hent := (entropy_convPow_le_and_asymptoticEntropy_eq_zero_of_virtuallyCyclic
    ⟨γ', hγ'o, hγ'fi⟩ (qS S) (qS_free S) T' hT' (p0 (qS S)) (p0_clopen _) (p0_sep _)
    (by norm_num : (1 : ℝ) < 2) hρ (Function.extend ι (μ : Gs → ℝ) 0) hfin' hprob' hsymm').2
  rw [asymptoticEntropy_extend ι hι] at hent
  -- Kaimanovich–Vershik on `Gs`
  have : Countable Gs := countable_of_fg Gs ⟨S0, hS0⟩
  have hprob : ErschlerZheng.IsProbability (μ : Gs → ℝ) := ⟨hμ.1, hμh⟩
  have hH : ErschlerZheng.HasFiniteEntropy (μ : Gs → ℝ) := by
    unfold ErschlerZheng.HasFiniteEntropy
    exact summable_of_ne_finset_zero (s := μ.support) fun g hg => by
      rw [Finsupp.notMem_support_iff.1 hg, Real.negMulLog_zero]
  have hnot := (KaimanovichVershik.not_hasNontrivialPoissonBoundary_iff_asymptoticEntropy_eq_zero
    (μ : Gs → ℝ) hprob hH).2 hent
  exact isLiouville_of_not μ hμ hs hnot

end JMMS.IETT110

namespace JMMS

theorem chk_isLiouville_of_rationalRank_eq_one_and_hasNontrivialBoundary_of_three_le_rationalRank
    (G : Subgroup (Equiv.Perm UnitAddCircle)) (hG : G ≤ IET) (hfg : G.FG) :
    (rationalRank (angleGroup G) = 1 →
      ∀ μ : ↥G →₀ ℝ, ThompsonAmenability.IsProbability μ → IsSymmetric μ →
        ThompsonAmenability.IsLiouville μ) ∧
    (3 ≤ rationalRank (angleGroup G) → (∀ a ∈ angleGroup G, rotation a ∈ G) →
      (∃ g ∈ G, ∀ a ∈ angleGroup G, g ≠ rotation a) →
      ∀ μ : ↥G →₀ ℝ, ThompsonAmenability.IsProbability μ → IsNondegenerate μ →
        HasNontrivialBoundary μ) :=
  ⟨fun h1 μ hμ hs => IETT110.isLiouville_of_rank_one G hG hfg h1 μ hμ hs,
    fun h3 hrot hnr μ hμ hnd => IETT110.hasNontrivialBoundary_of_rank G hG h3 hrot hnr μ hμ hnd⟩

end JMMS
end

open IntervalExchange
theorem solution
    (G : Subgroup (Equiv.Perm UnitAddCircle)) (hG : G ≤ IET) (hfg : G.FG) :
    (rationalRank (angleGroup G) = 1 →
      ∀ μ : ↥G →₀ ℝ, ThompsonAmenability.IsProbability μ → IsSymmetric μ →
        ThompsonAmenability.IsLiouville μ) ∧
    (3 ≤ rationalRank (angleGroup G) → (∀ a ∈ angleGroup G, rotation a ∈ G) →
      (∃ g ∈ G, ∀ a ∈ angleGroup G, g ≠ rotation a) →
      ∀ μ : ↥G →₀ ℝ, ThompsonAmenability.IsProbability μ → IsNondegenerate μ →
        HasNontrivialBoundary μ) :=
  JMMS.chk_isLiouville_of_rationalRank_eq_one_and_hasNontrivialBoundary_of_three_le_rationalRank G hG hfg
