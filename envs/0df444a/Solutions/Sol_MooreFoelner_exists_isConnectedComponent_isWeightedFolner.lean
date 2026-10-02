-- Prove2me | solution 1 for MooreFoelner.exists_isConnectedComponent_isWeightedFolner
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T06:32:47.358596+00:00
-- url     : https://prove2.me/submissions/444818dd-6bdf-4dcc-a8c8-f1a98ec02df5

import Definitions.Def_CannonFloydParry
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees
import Definitions.Def_ThompsonAmenability
import Mathlib

section
namespace MooreFoelner

open Classical CannonFloydParry

end MooreFoelner
end

section
/-!
# Moore 2013, §3 (group Sec3B): Remark 3.8, Lemmas 3.10, 3.12, 3.14, 3.15
-/

namespace MooreFoelner.Dev.Sec3B

open Classical MooreFoelner

set_option linter.unusedSectionVars false

variable {G S : Type*} [Group G]

/-! ## Marginal sets -/

/-! ## Mass, restriction and `valAt` -/

theorem mass_univ (μ : S →₀ ℝ) : mass μ Set.univ = ∑ s ∈ μ.support, μ s := by
  simp [mass]

theorem restrict_apply (μ : S →₀ ℝ) (A : Set S) (s : S) :
    restrict μ A s = if s ∈ A then μ s else 0 := by
  simp [restrict, Finsupp.filter_apply]

theorem support_restrict (μ : S →₀ ℝ) (A : Set S) :
    (restrict μ A).support = μ.support.filter (· ∈ A) := by
  simp [restrict, Finsupp.support_filter]

theorem support_restrict_subset (μ : S →₀ ℝ) (A : Set S) :
    (restrict μ A).support ⊆ μ.support := by
  rw [support_restrict]; exact Finset.filter_subset _ _

theorem restrict_nonneg {μ : S →₀ ℝ} (hμ : ∀ s, 0 ≤ μ s) (A : Set S) (s : S) :
    0 ≤ restrict μ A s := by
  rw [restrict_apply]; split_ifs <;> simp [hμ s]

theorem valAt_of_some {act : S → G → Option S} {μ : S →₀ ℝ} {s y : S} {g : G}
    (h : act s g = some y) : valAt act μ s g = μ y := by
  simp [valAt, h]

theorem valAt_of_none {act : S → G → Option S} {μ : S →₀ ℝ} {s : S} {g : G}
    (h : act s g = none) : valAt act μ s g = 0 := by
  simp [valAt, h]

theorem valAt_sum {ι : Type*} (act : S → G → Option S) (t : Finset ι) (f : ι → S →₀ ℝ) (s : S)
    (g : G) : valAt act (∑ i ∈ t, f i) s g = ∑ i ∈ t, valAt act (f i) s g := by
  cases h : act s g with
  | none => simp [valAt_of_none h]
  | some y => simp [valAt_of_some h, Finsupp.finsetSum_apply]

/-- The points sent into the support of `μ` by `γ`. -/
noncomputable def pre (act : S → G → Option S) (μ : S →₀ ℝ) (γ : G) : Finset S :=
  μ.support.biUnion fun y => (act y γ⁻¹).toFinset

theorem mem_pre {act : S → G → Option S} (hact : IsPartialAction act) {μ : S →₀ ℝ} {s y : S}
    {γ : G} (h : act s γ = some y) (hy : μ y ≠ 0) : s ∈ pre act μ γ := by
  rw [pre, Finset.mem_biUnion]
  refine ⟨y, Finsupp.mem_support_iff.mpr hy, ?_⟩
  rw [Option.mem_toFinset]
  exact (hact.inv γ s y).mp h

theorem support_abs_sub_subset {act : S → G → Option S} (hact : IsPartialAction act)
    {μ ν : S →₀ ℝ} (hsub : ν.support ⊆ μ.support) (γ : G) :
    Function.support (fun s => |valAt act ν s γ - ν s|) ⊆ ↑(μ.support ∪ pre act μ γ) := by
  intro s hs
  simp only [Function.mem_support, ne_eq, abs_eq_zero, sub_eq_zero] at hs
  rw [Finset.mem_coe]
  by_cases hνs : ν s = 0
  · cases h : act s γ with
    | none => rw [valAt_of_none h, hνs] at hs; exact absurd rfl hs
    | some y =>
      rw [valAt_of_some h, hνs] at hs
      have : y ∈ μ.support := hsub (Finsupp.mem_support_iff.mpr hs)
      exact Finset.mem_union_right _ (mem_pre hact h (Finsupp.mem_support_iff.mp this))
  · exact Finset.mem_union_left _ (hsub (Finsupp.mem_support_iff.mpr hνs))

theorem finsum_abs_sub_eq_sum {act : S → G → Option S} (hact : IsPartialAction act)
    {μ ν : S →₀ ℝ} (hsub : ν.support ⊆ μ.support) (γ : G) :
    ∑ᶠ s, |valAt act ν s γ - ν s| = ∑ s ∈ μ.support ∪ pre act μ γ, |valAt act ν s γ - ν s| :=
  finsum_eq_sum_of_support_subset _ (support_abs_sub_subset hact hsub γ)

/-! ## Weighted Følner sets -/

/-! ## Lemma 3.10 -/

/-! ## Γ-connected sets and components -/

/-- One step of a chain inside `A`. -/
def Step (act : S → G → Option S) (Γ : Finset G) (A : Set S) (x y : S) : Prop :=
  x ∈ A ∧ y ∈ A ∧ ∃ γ ∈ Γ, act x γ = some y

theorem isConnected_iff (act : S → G → Option S) (Γ : Finset G) (A : Set S) :
    IsConnected act Γ A ↔ ∀ x ∈ A, ∀ y ∈ A, Relation.ReflTransGen (Step act Γ A) x y := by
  constructor
  · intro h x hx y hy
    obtain ⟨l, p, h0, hl, hA, hstep⟩ := h x hx y hy
    have : ∀ i : Fin (l + 1), Relation.ReflTransGen (Step act Γ A) x (p i) := by
      intro i
      induction i using Fin.induction with
      | zero => rw [h0]
      | succ i ih =>
        obtain ⟨γ, hγ, h⟩ := hstep i
        exact ih.tail ⟨hA _, hA _, γ, hγ, h⟩
    simpa [hl] using this (Fin.last l)
  · intro h x hx y hy
    have key : ∀ z, Relation.ReflTransGen (Step act Γ A) x z → ∃ (l : ℕ) (p : Fin (l + 1) → S),
        p 0 = x ∧ p (Fin.last l) = z ∧ (∀ i, p i ∈ A) ∧
          ∀ i : Fin l, ∃ γ ∈ Γ, act (p i.castSucc) γ = some (p i.succ) := by
      intro z hz
      induction hz with
      | refl => exact ⟨0, fun _ => x, rfl, rfl, fun _ => hx, fun i => i.elim0⟩
      | @tail b c _ hbc ih =>
        obtain ⟨l, p, h0, hl, hA, hstep⟩ := ih
        obtain ⟨_, hc, γ, hγ, hbc'⟩ := hbc
        refine ⟨l + 1, Fin.snoc p c, ?_, ?_, ?_, ?_⟩
        · have : (0 : Fin (l + 2)) = Fin.castSucc (0 : Fin (l + 1)) := rfl
          rw [this, Fin.snoc_castSucc, h0]
        · rw [Fin.snoc_last]
        · intro i
          induction i using Fin.lastCases with
          | last => rw [Fin.snoc_last]; exact hc
          | cast i => rw [Fin.snoc_castSucc]; exact hA i
        · intro i
          induction i using Fin.lastCases with
          | last =>
            refine ⟨γ, hγ, ?_⟩
            have : (Fin.last l).succ = Fin.last (l + 1) := Fin.succ_last l
            rw [Fin.snoc_castSucc, this, Fin.snoc_last, hl]
            exact hbc'
          | cast i =>
            obtain ⟨γ', hγ', h'⟩ := hstep i
            refine ⟨γ', hγ', ?_⟩
            rw [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
            exact h'
    exact key y (h x hx y hy)

theorem step_symm {act : S → G → Option S} (hact : IsPartialAction act) {Γ : Finset G}
    (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) {A : Set S} {x y : S} (h : Step act Γ A x y) :
    Step act Γ A y x := by
  obtain ⟨hx, hy, γ, hγ, h⟩ := h
  exact ⟨hy, hx, γ⁻¹, hsymm γ hγ, (hact.inv γ x y).mp h⟩

theorem rtg_symm {act : S → G → Option S} (hact : IsPartialAction act) {Γ : Finset G}
    (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) {A : Set S} {x y : S}
    (h : Relation.ReflTransGen (Step act Γ A) x y) : Relation.ReflTransGen (Step act Γ A) y x := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact (Relation.ReflTransGen.single (step_symm hact hsymm hbc)).trans ih

theorem step_mono {act : S → G → Option S} {Γ : Finset G} {A B : Set S} (hAB : A ⊆ B) {x y : S}
    (h : Step act Γ A x y) : Step act Γ B x y :=
  ⟨hAB h.1, hAB h.2.1, h.2.2⟩

/-- The `Γ`-connected component of `x` in the support of `μ`. -/
noncomputable def comp (act : S → G → Option S) (Γ : Finset G) (μ : S →₀ ℝ) (x : S) : Finset S :=
  μ.support.filter (fun y => Relation.ReflTransGen (Step act Γ ↑μ.support) x y)

section comp

variable {act : S → G → Option S} {Γ : Finset G} {μ : S →₀ ℝ}

theorem mem_comp {x y : S} :
    y ∈ comp act Γ μ x ↔ y ∈ μ.support ∧ Relation.ReflTransGen (Step act Γ ↑μ.support) x y := by
  rw [comp, Finset.mem_filter]

theorem self_mem_comp {x : S} (hx : x ∈ μ.support) : x ∈ comp act Γ μ x :=
  mem_comp.mpr ⟨hx, .refl⟩

theorem comp_eq (hact : IsPartialAction act) (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) {x y : S}
    (hy : y ∈ comp act Γ μ x) : comp act Γ μ y = comp act Γ μ x := by
  have hxy := (mem_comp.mp hy).2
  ext z
  rw [mem_comp, mem_comp]
  constructor
  · rintro ⟨hz, h⟩; exact ⟨hz, hxy.trans h⟩
  · rintro ⟨hz, h⟩; exact ⟨hz, (rtg_symm hact hsymm hxy).trans h⟩

theorem comp_eq_of_act (hact : IsPartialAction act) (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) {s y : S} {γ : G}
    (hs : s ∈ μ.support) (hy : y ∈ μ.support) (hγ : γ ∈ Γ) (h : act s γ = some y) :
    comp act Γ μ y = comp act Γ μ s :=
  comp_eq hact hsymm (mem_comp.mpr ⟨hy, .single ⟨hs, hy, γ, hγ, h⟩⟩)

theorem isConnectedComponent_comp (hact : IsPartialAction act) (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ)
    {x : S} (hx : x ∈ μ.support) :
    IsConnectedComponent act Γ ↑(comp act Γ μ x) ↑μ.support := by
  refine ⟨fun y hy => (mem_comp.mp hy).1, ?_, ?_⟩
  · rw [isConnected_iff]
    intro y hy z hz
    have key : ∀ w, Relation.ReflTransGen (Step act Γ ↑μ.support) x w →
        Relation.ReflTransGen (Step act Γ ↑(comp act Γ μ x)) x w := by
      intro w hw
      induction hw with
      | refl => exact .refl
      | tail hxb hbc ih =>
        exact ih.tail ⟨mem_comp.mpr ⟨hbc.1, hxb⟩, mem_comp.mpr ⟨hbc.2.1, hxb.tail hbc⟩, hbc.2.2⟩
    have hy' := key y (mem_comp.mp hy).2
    have hz' := key z (mem_comp.mp hz).2
    exact (rtg_symm hact hsymm hy').trans hz'
  · intro A' hA' hA'B hconn
    refine Set.Subset.antisymm ?_ hA'
    intro z hz
    have hx' : x ∈ A' := hA' (self_mem_comp hx)
    have h1 := (isConnected_iff _ _ _).mp hconn x hx' z hz
    have h2 := Relation.ReflTransGen.mono (fun a b h => step_mono hA'B h) x z h1
    exact mem_comp.mpr ⟨hA'B hz, h2⟩

theorem sum_restrict_comp (hact : IsPartialAction act) (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) :
    ∑ K ∈ μ.support.image (comp act Γ μ), restrict μ ↑K = μ := by
  ext s
  rw [Finsupp.finsetSum_apply]
  simp_rw [restrict_apply, Finset.mem_coe]
  by_cases hs : s ∈ μ.support
  · rw [Finset.sum_eq_single_of_mem (comp act Γ μ s) (Finset.mem_image_of_mem _ hs)]
    · rw [if_pos (self_mem_comp hs)]
    · intro K hK hKs
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hK
      rw [if_neg]
      intro hsK
      exact hKs (comp_eq hact hsymm hsK).symm
  · rw [Finsupp.notMem_support_iff.mp hs]
    simp

theorem touch_of_ne_zero {s : S} {γ : G} {K : Finset S}
    (h : valAt act (restrict μ ↑K) s γ - restrict μ ↑K s ≠ 0) :
    s ∈ K ∨ ∃ y, act s γ = some y ∧ y ∈ K := by
  by_contra hc
  push Not at hc
  apply h
  have h1 : restrict μ ↑K s = 0 := by rw [restrict_apply, if_neg (by simpa using hc.1)]
  have h2 : valAt act (restrict μ ↑K) s γ = 0 := by
    cases ha : act s γ with
    | none => exact valAt_of_none ha
    | some y => rw [valAt_of_some ha, restrict_apply, if_neg (by simpa using hc.2 y ha)]
  rw [h1, h2, sub_zero]

theorem anchor (hact : IsPartialAction act) (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) {s : S} {γ : G}
    {K : Finset S} (hK : K ∈ μ.support.image (comp act Γ μ))
    (h : s ∈ K ∨ ∃ y, act s γ = some y ∧ y ∈ K) :
    (s ∈ μ.support ∧ K = comp act Γ μ s) ∨
      ∃ y, act s γ = some y ∧ y ∈ μ.support ∧ K = comp act Γ μ y := by
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hK
  rcases h with h | ⟨y, hy, h⟩
  · exact Or.inl ⟨(mem_comp.mp h).1, (comp_eq hact hsymm h).symm⟩
  · exact Or.inr ⟨y, hy, (mem_comp.mp h).1, (comp_eq hact hsymm h).symm⟩

theorem touch_unique (hact : IsPartialAction act) (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) {s : S} {γ : G}
    (hγ : γ ∈ Γ) {K K' : Finset S} (hK : K ∈ μ.support.image (comp act Γ μ))
    (hK' : K' ∈ μ.support.image (comp act Γ μ))
    (h : s ∈ K ∨ ∃ y, act s γ = some y ∧ y ∈ K)
    (h' : s ∈ K' ∨ ∃ y, act s γ = some y ∧ y ∈ K') : K = K' := by
  rcases anchor hact hsymm hK h with ⟨hs, rfl⟩ | ⟨y, hy, hys, rfl⟩ <;>
    rcases anchor hact hsymm hK' h' with ⟨hs', rfl⟩ | ⟨y', hy', hys', rfl⟩
  · rfl
  · exact (comp_eq_of_act hact hsymm hs hys' hγ hy').symm
  · exact comp_eq_of_act hact hsymm hs' hys hγ hy
  · rw [hy] at hy'; cases hy'; rfl

end comp

theorem sum_abs_eq_abs_sum {ι : Type*} (t : Finset ι) (a : ι → ℝ)
    (h : ∀ i ∈ t, ∀ j ∈ t, a i ≠ 0 → a j ≠ 0 → i = j) :
    ∑ i ∈ t, |a i| = |∑ i ∈ t, a i| := by
  by_cases hex : ∃ i ∈ t, a i ≠ 0
  · obtain ⟨i, hi, hai⟩ := hex
    have hz : ∀ j ∈ t, j ≠ i → a j = 0 := fun j hj hji => by
      by_contra hj0; exact hji (h j hj i hi hj0 hai)
    rw [Finset.sum_eq_single_of_mem i hi (fun j hj hji => by rw [hz j hj hji, abs_zero]),
      Finset.sum_eq_single_of_mem i hi hz]
  · push Not at hex
    rw [Finset.sum_eq_zero (fun i hi => by rw [hex i hi, abs_zero]), Finset.sum_eq_zero hex,
      abs_zero]

theorem sum_comp_abs {act : S → G → Option S} (hact : IsPartialAction act) {Γ : Finset G}
    (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) (μ : S →₀ ℝ) (s : S) {γ : G} (hγ : γ ∈ Γ) :
    ∑ K ∈ μ.support.image (comp act Γ μ),
        |valAt act (restrict μ ↑K) s γ - restrict μ ↑K s| = |valAt act μ s γ - μ s| := by
  rw [sum_abs_eq_abs_sum]
  · rw [Finset.sum_sub_distrib, ← valAt_sum, ← Finsupp.finsetSum_apply,
      sum_restrict_comp hact hsymm]
  · intro K hK K' hK' h h'
    exact touch_unique hact hsymm hγ hK hK' (touch_of_ne_zero h) (touch_of_ne_zero h')

/-! ## The right action of `G` on itself -/

end MooreFoelner.Dev.Sec3B

namespace MooreFoelner

open Classical CannonFloydParry

end MooreFoelner
end

open MooreFoelner in
open Classical MooreFoelner in
open Classical CannonFloydParry in
open MooreFoelner.Dev.Sec3B in
theorem solution {G S : Type*} [Group G]
    (act : S → G → Option S) (hact : IsPartialAction act) (Γ : Finset G)
    (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) (hgen : Subgroup.closure (Γ : Set G) = ⊤) (ε : ℝ) (hε : 0 < ε)
    (μ : S →₀ ℝ) (hμ : IsWeightedFolner act Γ μ ε) :
    ∃ A : Set S, IsConnectedComponent act Γ A ↑μ.support ∧
      IsWeightedFolner act Γ (restrict μ A) ε := by
  set comps := μ.support.image (comp act Γ μ) with hcomps
  have hF : ∑ γ ∈ Γ, ∑ᶠ s, |valAt act μ s γ - μ s| =
      ∑ K ∈ comps, ∑ γ ∈ Γ, ∑ᶠ s, |valAt act (restrict μ ↑K) s γ - restrict μ ↑K s| := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    rw [finsum_abs_sub_eq_sum hact subset_rfl]
    simp_rw [finsum_abs_sub_eq_sum hact (support_restrict_subset μ _)]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => (sum_comp_abs hact hsymm μ s hγ).symm
  have hM : mass μ Set.univ = ∑ K ∈ comps, mass (restrict μ ↑K) Set.univ := by
    have : ∀ K : Finset S, mass (restrict μ ↑K) Set.univ = ∑ s ∈ μ.support, restrict μ ↑K s := by
      intro K
      rw [mass_univ]
      exact Finset.sum_subset (support_restrict_subset μ _)
        (fun s _ hs => Finsupp.notMem_support_iff.mp hs)
    simp_rw [this]
    rw [Finset.sum_comm, mass_univ]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finsupp.finsetSum_apply, sum_restrict_comp hact hsymm]
  have h := hμ.2
  rw [hF, hM, Finset.mul_sum] at h
  obtain ⟨K, hK, hlt⟩ := Finset.exists_lt_of_sum_lt h
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hK
  exact ⟨↑(comp act Γ μ x), isConnectedComponent_comp hact hsymm hx,
    restrict_nonneg hμ.1 _, hlt⟩
