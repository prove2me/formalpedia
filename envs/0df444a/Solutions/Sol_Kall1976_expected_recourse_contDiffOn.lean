-- Prove2me | solution 1 for Kall1976.expected_recourse_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T22:29:29.24989+00:00
-- url     : https://prove2.me/submissions/6aa9c6ff-b802-4476-888b-104d438f70ff

import Definitions.Def_Kall1976_RecourseDifferentiability

open MeasureTheory
open scoped Matrix

namespace Kall1976

section LPBsec
namespace LPB

open Matrix

set_option linter.unusedSectionVars false

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

def PFeas (M : Matrix κ ι ℝ) (r : κ → ℝ) (z : ι → ℝ) : Prop := (∀ j, 0 ≤ z j) ∧ M *ᵥ z = r

noncomputable def supp (z : ι → ℝ) : Finset ι := Finset.univ.filter (fun j => z j ≠ 0)

def ColLI (M : Matrix κ ι ℝ) (S : Finset ι) : Prop :=
  LinearIndependent ℝ (fun j : S => Mᵀ (j : ι))

lemma mem_supp {z : ι → ℝ} {j : ι} : j ∈ supp z ↔ z j ≠ 0 := by simp [supp]

lemma sum_sub_eq_mulVec (M : Matrix κ ι ℝ) (S : Finset ι) (w : ι → ℝ)
    (hw : ∀ j, j ∉ S → w j = 0) :
    ∑ j : S, w j • Mᵀ (j : ι) = M *ᵥ w := by
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, transpose_apply, smul_eq_mul, mulVec, dotProduct]
  rw [Finset.sum_coe_sort S (fun j => w j * M i j)]
  rw [Finset.sum_subset (Finset.subset_univ S)]
  · exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  · intro j _ hj; simp [hw j hj]

lemma reduce (M : Matrix κ ι ℝ) (r : κ → ℝ) (c : ι → ℝ) (L : ℝ)
    (hL : ∀ z, PFeas M r z → L ≤ c ⬝ᵥ z) :
    ∀ n, ∀ z, (supp z).card = n → PFeas M r z →
      ∃ z', PFeas M r z' ∧ c ⬝ᵥ z' ≤ c ⬝ᵥ z ∧ supp z' ⊆ supp z ∧ ColLI M (supp z') := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro z hn hz
  by_cases hli : ColLI M (supp z)
  · exact ⟨z, hz, le_rfl, subset_rfl, hli⟩
  obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hli
  let d : ι → ℝ := fun j => if h : j ∈ supp z then g ⟨j, h⟩ else 0
  have hdS : ∀ j, j ∉ supp z → d j = 0 := by intro j hj; simp [d, hj]
  have hMd : M *ᵥ d = 0 := by
    rw [← sum_sub_eq_mulVec M (supp z) d hdS]
    convert hg using 2 with j
    simp [d]
  have hdi0 : d i0 ≠ 0 := by simpa [d] using hi0
  have hzpos : ∀ j, 0 ≤ z j := hz.1
  -- unboundedness contradiction
  have unb : ∀ e : ι → ℝ, M *ᵥ e = 0 → (∀ j, 0 ≤ e j) → c ⬝ᵥ e < 0 → False := by
    intro e hMe he hce
    set s := (c ⬝ᵥ z - L + 1) / (-(c ⬝ᵥ e)) with hs
    have hs0 : 0 ≤ s := div_nonneg (by linarith [hL z hz]) (by linarith)
    have hf : PFeas M r (z + s • e) := ⟨fun j => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (hzpos j) (mul_nonneg hs0 (he j)), by
      rw [mulVec_add, mulVec_smul, hMe, smul_zero, add_zero, hz.2]⟩
    have := hL _ hf
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at this
    have hse : s * (c ⬝ᵥ e) = -(c ⬝ᵥ z - L + 1) := by
      have hne : -(c ⬝ᵥ e) ≠ 0 := by linarith
      have h2 : (c ⬝ᵥ z - L + 1) / -(c ⬝ᵥ e) * -(c ⬝ᵥ e) = c ⬝ᵥ z - L + 1 := div_mul_cancel₀ _ hne
      rw [hs]; linear_combination -h2
    linarith
  obtain ⟨e, hMe, heS, hce, j0, hj0⟩ : ∃ e : ι → ℝ, M *ᵥ e = 0 ∧ (∀ j, j ∉ supp z → e j = 0) ∧
      c ⬝ᵥ e ≤ 0 ∧ ∃ j, e j < 0 := by
    obtain ⟨d1, hMd1, hd1S, hcd1, hd1i0⟩ : ∃ d1 : ι → ℝ, M *ᵥ d1 = 0 ∧
        (∀ j, j ∉ supp z → d1 j = 0) ∧ c ⬝ᵥ d1 ≤ 0 ∧ d1 i0 ≠ 0 := by
      by_cases h : c ⬝ᵥ d ≤ 0
      · exact ⟨d, hMd, hdS, h, hdi0⟩
      · refine ⟨-d, by rw [mulVec_neg, hMd, neg_zero], fun j hj => by simp [hdS j hj], ?_, ?_⟩
        · rw [dotProduct_neg]; linarith
        · simpa using hdi0
    by_cases hneg : ∃ j, d1 j < 0
    · exact ⟨d1, hMd1, hd1S, hcd1, hneg⟩
    push_neg at hneg
    rcases hcd1.lt_or_eq with hlt | heq
    · exact (unb d1 hMd1 hneg hlt).elim
    · refine ⟨-d1, by rw [mulVec_neg, hMd1, neg_zero], fun j hj => by simp [hd1S j hj],
        by rw [dotProduct_neg, heq, neg_zero], i0, ?_⟩
      have := lt_of_le_of_ne (hneg i0) (Ne.symm hd1i0)
      simp only [Pi.neg_apply]; linarith
  let P := Finset.univ.filter (fun j => e j < 0)
  obtain ⟨jm, hjmP, hjm⟩ := P.exists_min_image (fun j => z j / (-e j)) ⟨j0, by simp [P, hj0]⟩
  have hejm : e jm < 0 := by simpa [P] using hjmP
  set t := z jm / (-e jm) with ht
  have ht0 : 0 ≤ t := div_nonneg (hzpos jm) (by linarith)
  let z' := z + t • e
  have hz' : PFeas M r z' := by
    refine ⟨fun j => ?_, by simp only [z']; rw [mulVec_add, mulVec_smul, hMe, smul_zero, add_zero, hz.2]⟩
    simp only [z', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hej : e j < 0
    · have h1 : t ≤ z j / (-e j) := hjm j (by simp [P, hej])
      rw [le_div_iff₀ (by linarith)] at h1
      linarith
    · push_neg at hej
      exact add_nonneg (hzpos j) (mul_nonneg ht0 hej)
  have hsub : supp z' ⊆ supp z := by
    intro j hj
    rw [mem_supp] at hj ⊢
    intro hzj
    apply hj
    have : e j = 0 := by
      by_contra hne
      exact absurd (heS j) (by
        intro h'
        have : j ∉ supp z := by rw [mem_supp]; exact fun h => h hzj
        exact hne (h' this))
    simp [z', hzj, this]
  have hjm_in : jm ∈ supp z := by
    by_contra h; exact absurd (heS jm h) (ne_of_lt hejm)
  have hjm_out : jm ∉ supp z' := by
    rw [mem_supp, not_not]
    simp only [z', Pi.add_apply, Pi.smul_apply, smul_eq_mul, ht]
    have hne : e jm ≠ 0 := ne_of_lt hejm
    rw [div_neg, neg_mul, div_mul_cancel₀ _ hne]; ring
  have hlt : (supp z').card < n := by
    rw [← hn]
    exact Finset.card_lt_card ⟨hsub, fun h => hjm_out (h hjm_in)⟩
  obtain ⟨z'', h1, h2, h3, h4⟩ := ih _ hlt z' rfl hz'
  refine ⟨z'', h1, le_trans h2 ?_, h3.trans hsub, h4⟩
  simp only [z', dotProduct_add, dotProduct_smul, smul_eq_mul]
  nlinarith

lemma colLI_unique (M : Matrix κ ι ℝ) (z1 z2 : ι → ℝ) (h : supp z1 = supp z2)
    (hli : ColLI M (supp z1)) (hM : M *ᵥ z1 = M *ᵥ z2) : z1 = z2 := by
  have hw : ∀ j, j ∉ supp z1 → (z1 - z2) j = 0 := by
    intro j hj
    have hj2 : j ∉ supp z2 := h ▸ hj
    rw [mem_supp, not_not] at hj hj2
    simp [hj, hj2]
  have hsum := sum_sub_eq_mulVec M (supp z1) (z1 - z2) hw
  rw [mulVec_sub, hM, sub_self] at hsum
  have := Fintype.linearIndependent_iff.mp hli (fun j => (z1 - z2) j) hsum
  funext j
  by_cases hj : j ∈ supp z1
  · have := this ⟨j, hj⟩; simp only [Pi.sub_apply] at this; linarith
  · have := hw j hj; simp only [Pi.sub_apply] at this; linarith

lemma attain (M : Matrix κ ι ℝ) (r : κ → ℝ) (c : ι → ℝ) (L : ℝ)
    (hL : ∀ z, PFeas M r z → L ≤ c ⬝ᵥ z) (z0 : ι → ℝ) (hz0 : PFeas M r z0) :
    ∃ zs, PFeas M r zs ∧ ColLI M (supp zs) ∧ ∀ z, PFeas M r z → c ⬝ᵥ zs ≤ c ⬝ᵥ z := by
  let F : Set (ι → ℝ) := {z | PFeas M r z ∧ ColLI M (supp z)}
  have hinj : Set.InjOn supp F := by
    intro z1 h1 z2 h2 h
    exact colLI_unique M z1 z2 h h1.2 (by rw [h1.1.2, h2.1.2])
  have hfin : F.Finite := Set.Finite.of_finite_image (Set.toFinite _) hinj
  obtain ⟨z1, hz1, _, _, hz1li⟩ := reduce M r c L hL _ z0 rfl hz0
  obtain ⟨zs, hzs, hmin⟩ := Set.exists_min_image F (fun z => c ⬝ᵥ z) hfin ⟨z1, hz1, hz1li⟩
  refine ⟨zs, hzs.1, hzs.2, fun z hz => ?_⟩
  obtain ⟨z', hz', hc', _, hli'⟩ := reduce M r c L hL _ z rfl hz
  exact le_trans (hmin z' ⟨hz', hli'⟩) hc'


def cone (M : Matrix κ ι ℝ) : Set (κ → ℝ) := (M.mulVecLin) '' {z | ∀ j, 0 ≤ z j}

lemma cone_closed (M : Matrix κ ι ℝ) : IsClosed (cone M) := by
  have heq : cone M = ⋃ (S : Finset ι) (_ : ColLI M S),
      (Fintype.linearCombination ℝ (fun j : S => Mᵀ (j : ι))) '' {w | ∀ j, 0 ≤ w j} := by
    ext t
    simp only [cone, Set.mem_image, Set.mem_setOf_eq, Set.mem_iUnion, mulVecLin_apply]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨z', hz', _, _, hli⟩ := reduce M (M *ᵥ z) 0 0 (fun _ _ => by simp) _ z rfl ⟨hz, rfl⟩
      refine ⟨supp z', hli, fun j => z' j, fun j => hz'.1 j, ?_⟩
      rw [Fintype.linearCombination_apply, sum_sub_eq_mulVec M (supp z') z'
        (fun j hj => by rw [mem_supp, not_not] at hj; exact hj), hz'.2]
    · rintro ⟨S, _, w, hw, rfl⟩
      refine ⟨fun j => if h : j ∈ S then w ⟨j, h⟩ else 0, fun j => ?_, ?_⟩
      · by_cases h : j ∈ S <;> simp [h, hw]
      · rw [Fintype.linearCombination_apply, ← sum_sub_eq_mulVec M S _ (fun j hj => by simp [hj])]
        simp
  rw [heq]
  apply isClosed_iUnion_of_finite
  intro S
  apply isClosed_iUnion_of_finite
  intro hli
  have hinj := linearIndependent_iff_injective_fintypeLinearCombination.mp hli
  have hker : LinearMap.ker (Fintype.linearCombination ℝ (fun j : S => Mᵀ (j : ι))) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  apply (LinearMap.isClosedEmbedding_of_injective hker).isClosedMap
  have : {w : S → ℝ | ∀ j, 0 ≤ w j} = ⋂ j, {w | 0 ≤ w j} := by ext; simp
  rw [this]
  exact isClosed_iInter (fun j => isClosed_le continuous_const (continuous_apply j))

lemma farkas (M : Matrix κ ι ℝ) (t : κ → ℝ) (ht : t ∉ cone M) :
    ∃ y : κ → ℝ, (∀ j, 0 ≤ (y ᵥ* M) j) ∧ y ⬝ᵥ t < 0 := by
  have hconv : Convex ℝ (cone M) := by
    apply Convex.linear_image
    have : {z : ι → ℝ | ∀ j, 0 ≤ z j} = Set.Ici 0 := by ext; simp [Pi.le_def]
    rw [this]; exact convex_Ici 0
  obtain ⟨f, u, hfu, hut⟩ := geometric_hahn_banach_closed_point hconv (cone_closed M) ht
  have h0 : 0 < u := by
    have := hfu 0 ⟨0, fun _ => le_rfl, by simp⟩
    simpa using this
  have hneg : ∀ a ∈ cone M, f a ≤ 0 := by
    intro a ha
    by_contra h
    push_neg at h
    obtain ⟨z, hz, rfl⟩ := ha
    have hs : 0 ≤ u / f (M.mulVecLin z) + 1 := by positivity
    have hmem : (u / f (M.mulVecLin z) + 1) • M.mulVecLin z ∈ cone M :=
      ⟨(u / f (M.mulVecLin z) + 1) • z, fun j => by
        simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hs (hz j), by simp⟩
    have := hfu _ hmem
    rw [map_smul, smul_eq_mul, add_mul, div_mul_cancel₀ _ (ne_of_gt h)] at this
    linarith
  have hf : ∀ v : κ → ℝ, f v = ∑ i, v i * f (fun j => if i = j then 1 else 0) := by
    intro v
    have := LinearMap.pi_apply_eq_sum_univ f.toLinearMap v
    simpa using this
  refine ⟨fun i => - f (fun j => if i = j then 1 else 0), fun j => ?_, ?_⟩
  · have hmem : Mᵀ j ∈ cone M := ⟨Pi.single j 1, fun k => by
      by_cases h : k = j
      · subst h; simp
      · simp [h], by ext i; simp [mulVec, dotProduct, Pi.single_apply]⟩
    have := hneg _ hmem
    rw [hf] at this
    simp only [vecMul, dotProduct, transpose_apply] at this ⊢
    have : ∑ x, -f (fun j => if x = j then 1 else 0) * M x j =
        -∑ x, M x j * f (fun j => if x = j then 1 else 0) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    linarith
  · have := hf t
    simp only [dotProduct]
    have : ∑ x, -f (fun j => if x = j then 1 else 0) * t x =
        -∑ x, t x * f (fun j => if x = j then 1 else 0) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    linarith

lemma weak_dual (M : Matrix κ ι ℝ) (r : κ → ℝ) (c : ι → ℝ) (π : κ → ℝ)
    (hπ : ∀ j, (π ᵥ* M) j ≤ c j) (z : ι → ℝ) (hz : PFeas M r z) : π ⬝ᵥ r ≤ c ⬝ᵥ z := by
  rw [← hz.2, dotProduct_mulVec]
  simp only [dotProduct]
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hπ j) (hz.1 j))

lemma dual_approx (M : Matrix κ ι ℝ) (r : κ → ℝ) (c : ι → ℝ) (zs : ι → ℝ) (hzs : PFeas M r zs)
    (hmin : ∀ z, PFeas M r z → c ⬝ᵥ zs ≤ c ⬝ᵥ z) (ε : ℝ) (hε : 0 < ε) :
    ∃ π : κ → ℝ, (∀ j, (π ᵥ* M) j ≤ c j) ∧ c ⬝ᵥ zs - ε < π ⬝ᵥ r := by
  let M' : Matrix (Option κ) (Option ι) ℝ := fun o o' => match o, o' with
    | none, none => 1
    | none, some j => c j
    | some _, none => 0
    | some i, some j => M i j
  let t' : Option κ → ℝ := fun o => match o with
    | none => c ⬝ᵥ zs - ε
    | some i => r i
  have hnot : t' ∉ cone M' := by
    rintro ⟨z', hz', hMz⟩
    have hrow : ∀ i, (M' *ᵥ z') (some i) = (M *ᵥ fun j => z' (some j)) i := by
      intro i; simp [M', mulVec, dotProduct, Fintype.sum_option]
    have hnone : (M' *ᵥ z') none = z' none + c ⬝ᵥ (fun j => z' (some j)) := by
      simp [M', mulVec, dotProduct, Fintype.sum_option]
    have hf : PFeas M r (fun j => z' (some j)) := ⟨fun j => hz' _, by
      funext i; rw [← hrow]; simp only [mulVecLin_apply] at hMz; rw [hMz]⟩
    have h1 := hmin _ hf
    simp only [mulVecLin_apply] at hMz
    have h2 := hnone
    rw [hMz] at h2
    simp only [t'] at h2
    have := hz' none
    linarith
  obtain ⟨y', hy', hyt⟩ := farkas M' t' hnot
  set μ := y' none
  let yy : κ → ℝ := fun i => y' (some i)
  have hμ : 0 ≤ μ := by
    have := hy' none
    simpa [M', vecMul, dotProduct, Fintype.sum_option] using this
  have hcol : ∀ j, 0 ≤ μ * c j + (yy ᵥ* M) j := by
    intro j
    have := hy' (some j)
    simpa [M', vecMul, dotProduct, Fintype.sum_option, yy] using this
  have hyt' : μ * (c ⬝ᵥ zs - ε) + yy ⬝ᵥ r < 0 := by
    simpa [t', dotProduct, Fintype.sum_option, yy] using hyt
  rcases hμ.lt_or_eq with hμp | hμ0
  · refine ⟨-(1 / μ) • yy, fun j => ?_, ?_⟩
    · rw [smul_vecMul, Pi.smul_apply, smul_eq_mul]
      have := hcol j
      rw [neg_mul, neg_le, div_mul_eq_mul_div, one_mul, le_div_iff₀ hμp]
      linarith
    · rw [smul_dotProduct, smul_eq_mul, neg_mul, lt_neg, div_mul_eq_mul_div, one_mul,
        div_lt_iff₀ hμp]
      linarith
  · exfalso
    rw [← hμ0] at hcol hyt'
    have := weak_dual M r 0 (-yy) (fun j => by
      rw [neg_vecMul, Pi.neg_apply]; have := hcol j; simp at this ⊢; linarith) zs hzs
    simp [neg_dotProduct] at this
    linarith


noncomputable def tight (M : Matrix κ ι ℝ) (c : ι → ℝ) (π : κ → ℝ) : Finset ι :=
  Finset.univ.filter (fun j => (π ᵥ* M) j = c j)

lemma vertex (M : Matrix κ ι ℝ) (hrow : ∀ d, d ᵥ* M = 0 → d = 0) (r : κ → ℝ) (c : ι → ℝ)
    (z0 : ι → ℝ) (hz0 : PFeas M r z0) :
    ∀ n, ∀ π : κ → ℝ, (Finset.univ.filter (fun j => (π ᵥ* M) j ≠ c j)).card = n →
      (∀ j, (π ᵥ* M) j ≤ c j) →
      ∃ π', (∀ j, (π' ᵥ* M) j ≤ c j) ∧ π ⬝ᵥ r ≤ π' ⬝ᵥ r ∧
        Submodule.span ℝ (Set.range (fun j : tight M c π' => Mᵀ (j : ι))) = ⊤ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro π hn hπ
  by_cases hspan : Submodule.span ℝ (Set.range (fun j : tight M c π => Mᵀ (j : ι))) = ⊤
  · exact ⟨π, hπ, le_rfl, hspan⟩
  obtain ⟨f, hf0, hfker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hspan)
  let d : κ → ℝ := fun i => f (fun j => if i = j then 1 else 0)
  have hfd : ∀ v, f v = v ⬝ᵥ d := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ f v]
    simp [dotProduct, d]
  have hdne : d ≠ 0 := by
    intro h; apply hf0; ext v; simp [hfd, h]
  have hdM : d ᵥ* M ≠ 0 := fun h => hdne (hrow d h)
  have hvm : ∀ (e : κ → ℝ) j, (e ᵥ* M) j = Mᵀ j ⬝ᵥ e := by
    intro e j; simp [vecMul, dotProduct, mul_comm]
  have htight0 : ∀ j ∈ tight M c π, (d ᵥ* M) j = 0 := by
    intro j hj
    have : Mᵀ j ∈ LinearMap.ker f := hfker (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
    rw [LinearMap.mem_ker, hfd] at this
    rw [hvm]; exact this
  have hbdd : ∀ π' : κ → ℝ, (∀ j, (π' ᵥ* M) j ≤ c j) → π' ⬝ᵥ r ≤ c ⬝ᵥ z0 :=
    fun π' h => weak_dual M r c π' h z0 hz0
  have unb : ∀ e : κ → ℝ, 0 < e ⬝ᵥ r → (∀ j, (e ᵥ* M) j ≤ 0) → False := by
    intro e her he
    set s := (c ⬝ᵥ z0 - π ⬝ᵥ r + 1) / (e ⬝ᵥ r) with hs
    have hs0 : 0 ≤ s := div_nonneg (by linarith [hbdd π hπ]) her.le
    have := hbdd (π + s • e) (fun j => by
      rw [add_vecMul, smul_vecMul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [hπ j, he j])
    rw [add_dotProduct, smul_dotProduct, smul_eq_mul] at this
    have h2 : (c ⬝ᵥ z0 - π ⬝ᵥ r + 1) / (e ⬝ᵥ r) * (e ⬝ᵥ r) = c ⬝ᵥ z0 - π ⬝ᵥ r + 1 :=
      div_mul_cancel₀ _ (ne_of_gt her)
    rw [← hs] at h2
    linarith
  obtain ⟨e, he0, her, j0, hj0⟩ : ∃ e : κ → ℝ, (∀ j ∈ tight M c π, (e ᵥ* M) j = 0) ∧
      0 ≤ e ⬝ᵥ r ∧ ∃ j, 0 < (e ᵥ* M) j := by
    obtain ⟨d1, hd10, hd1r, hd1M⟩ : ∃ d1 : κ → ℝ, (∀ j ∈ tight M c π, (d1 ᵥ* M) j = 0) ∧
        0 ≤ d1 ⬝ᵥ r ∧ d1 ᵥ* M ≠ 0 := by
      by_cases h : 0 ≤ d ⬝ᵥ r
      · exact ⟨d, htight0, h, hdM⟩
      · refine ⟨-d, fun j hj => by rw [neg_vecMul, Pi.neg_apply, htight0 j hj, neg_zero],
          by rw [neg_dotProduct]; linarith, by rw [neg_vecMul]; exact neg_ne_zero.mpr hdM⟩
    by_cases hpos : ∃ j, 0 < (d1 ᵥ* M) j
    · exact ⟨d1, hd10, hd1r, hpos⟩
    push_neg at hpos
    rcases hd1r.lt_or_eq with hlt | heq
    · exact (unb d1 hlt hpos).elim
    · obtain ⟨j1, hj1⟩ : ∃ j, (d1 ᵥ* M) j ≠ 0 := by
        by_contra h; push_neg at h; exact hd1M (funext h)
      refine ⟨-d1, fun j hj => by rw [neg_vecMul, Pi.neg_apply, hd10 j hj, neg_zero],
        by rw [neg_dotProduct, ← heq, neg_zero], j1, ?_⟩
      rw [neg_vecMul, Pi.neg_apply]
      have := lt_of_le_of_ne (hpos j1) hj1
      linarith
  let P := Finset.univ.filter (fun j => 0 < (e ᵥ* M) j)
  obtain ⟨jm, hjmP, hjm⟩ := P.exists_min_image (fun j => (c j - (π ᵥ* M) j) / (e ᵥ* M) j)
    ⟨j0, by simp [P, hj0]⟩
  have hejm : 0 < (e ᵥ* M) jm := by simpa [P] using hjmP
  set t := (c jm - (π ᵥ* M) jm) / (e ᵥ* M) jm with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith [hπ jm]) hejm.le
  set π' := π + t • e with hπ'
  have hvm' : ∀ j, (π' ᵥ* M) j = (π ᵥ* M) j + t * (e ᵥ* M) j := by
    intro j; rw [hπ', add_vecMul, smul_vecMul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hπ'f : ∀ j, (π' ᵥ* M) j ≤ c j := by
    intro j
    rw [hvm']
    by_cases hej : 0 < (e ᵥ* M) j
    · have h1 : t ≤ (c j - (π ᵥ* M) j) / (e ᵥ* M) j := hjm j (by simp [P, hej])
      rw [le_div_iff₀ hej] at h1
      linarith
    · push_neg at hej
      nlinarith [hπ j]
  have hjm_t : (π' ᵥ* M) jm = c jm := by
    rw [hvm', ht, div_mul_cancel₀ _ (ne_of_gt hejm)]; ring
  have hsub : Finset.univ.filter (fun j => (π' ᵥ* M) j ≠ c j) ⊂
      Finset.univ.filter (fun j => (π ᵥ* M) j ≠ c j) := by
    refine ⟨fun j hj => ?_, fun h => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      intro htj
      apply hj
      have : j ∈ tight M c π := by simp [tight, htj]
      rw [hvm', he0 j this, mul_zero, add_zero, htj]
    · have : jm ∈ Finset.univ.filter (fun j => (π ᵥ* M) j ≠ c j) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro htj
        have : jm ∈ tight M c π := by simp [tight, htj]
        linarith [he0 jm this]
      have := h this
      simp [hjm_t] at this
  obtain ⟨π'', h1, h2, h3⟩ := ih _ (hn ▸ Finset.card_lt_card hsub) π' rfl hπ'f
  refine ⟨π'', h1, le_trans ?_ h2, h3⟩
  rw [hπ', add_dotProduct, smul_dotProduct, smul_eq_mul]
  nlinarith

lemma extract {m : ℕ} (M : Matrix (Fin m) ι ℝ) (c : ι → ℝ) (π : Fin m → ℝ)
    (hspan : Submodule.span ℝ (Set.range (fun j : tight M c π => Mᵀ (j : ι))) = ⊤) :
    ∃ b : Fin m → ι, Function.Injective b ∧ IsUnit (M.submatrix id b) ∧
      π = ((M.submatrix id b)ᵀ)⁻¹ *ᵥ (fun i => c (b i)) := by
  obtain ⟨κ', a, ha, hsp, hli⟩ := exists_linearIndependent' ℝ (fun j : tight M c π => Mᵀ (j : ι))
  have hfin : Finite κ' := Finite.of_injective a ha
  have : Fintype κ' := Fintype.ofFinite κ'
  let B := Module.Basis.mk hli (by rw [hsp, hspan])
  have hcard : Fintype.card κ' = m := by
    have := Module.finrank_eq_card_basis B
    simpa using this.symm
  let e : Fin m ≃ κ' := (Fintype.equivFinOfCardEq hcard).symm
  let b : Fin m → ι := fun i => ((a (e i)) : ι)
  have hb : Function.Injective b := by
    intro i1 i2 h
    exact e.injective (ha (Subtype.ext h))
  have hunit : IsUnit (M.submatrix id b) := by
    rw [← linearIndependent_cols_iff_isUnit]
    have := hli.comp e e.injective
    have heq : (M.submatrix id b).col = ((fun j : tight M c π => Mᵀ (j : ι)) ∘ a) ∘ e := by
      funext i k; simp [b, Matrix.col]
    rw [heq]; exact this
  have htb : ∀ i, (π ᵥ* M) (b i) = c (b i) := by
    intro i
    have := (a (e i)).2
    simpa [tight] using this
  refine ⟨b, hb, hunit, ?_⟩
  have hU : IsUnit ((M.submatrix id b)ᵀ).det := by
    rw [det_transpose]; exact (isUnit_iff_isUnit_det _).mp hunit
  have hv : (M.submatrix id b)ᵀ *ᵥ π = fun i => c (b i) := by
    funext i
    rw [← htb i]
    simp [vecMul, mulVec, dotProduct, mul_comm]
  rw [← hv, mulVec_mulVec, nonsing_inv_mul _ hU, one_mulVec]

theorem lpb {m : ℕ} (M : Matrix (Fin m) ι ℝ) (hrow : ∀ d, d ᵥ* M = 0 → d = 0)
    (r : Fin m → ℝ) (c : ι → ℝ) (L : ℝ) (hL : ∀ z, PFeas M r z → L ≤ c ⬝ᵥ z)
    (z0 : ι → ℝ) (hz0 : PFeas M r z0) :
    ∃ b : Fin m → ι, Function.Injective b ∧
      (∀ j, ((((M.submatrix id b)ᵀ)⁻¹ *ᵥ (fun i => c (b i))) ᵥ* M) j ≤ c j) ∧
      ∃ zs, PFeas M r zs ∧ (∀ z, PFeas M r z → c ⬝ᵥ zs ≤ c ⬝ᵥ z) ∧
        c ⬝ᵥ zs = (((M.submatrix id b)ᵀ)⁻¹ *ᵥ (fun i => c (b i))) ⬝ᵥ r := by
  classical
  obtain ⟨zs, hzs, -, hmin⟩ := attain M r c L hL z0 hz0
  let πb : (Fin m → ι) → (Fin m → ℝ) := fun b => ((M.submatrix id b)ᵀ)⁻¹ *ᵥ (fun i => c (b i))
  have key : ∀ ε, 0 < ε → ∃ b : Fin m → ι, Function.Injective b ∧
      (∀ j, (πb b ᵥ* M) j ≤ c j) ∧ c ⬝ᵥ zs - ε < πb b ⬝ᵥ r := by
    intro ε hε
    obtain ⟨π, hπ, hπr⟩ := dual_approx M r c zs hzs hmin ε hε
    obtain ⟨π', hπ', hle, hspan⟩ := vertex M hrow r c zs hzs _ π rfl hπ
    obtain ⟨b, hb, -, hbeq⟩ := extract M c π' hspan
    refine ⟨b, hb, ?_, ?_⟩
    · show ∀ j, ((((M.submatrix id b)ᵀ)⁻¹ *ᵥ (fun i => c (b i))) ᵥ* M) j ≤ c j
      rw [← hbeq]; exact hπ'
    · show c ⬝ᵥ zs - ε < (((M.submatrix id b)ᵀ)⁻¹ *ᵥ (fun i => c (b i))) ⬝ᵥ r
      rw [← hbeq]; linarith
  let S := Finset.univ.filter (fun b : Fin m → ι => Function.Injective b ∧ ∀ j, (πb b ᵥ* M) j ≤ c j)
  by_contra hcon
  have hlt : ∀ b ∈ S, πb b ⬝ᵥ r < c ⬝ᵥ zs := by
    intro b hb
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have h1 := weak_dual M r c (πb b) hb.2 zs hzs
    rcases h1.lt_or_eq with h | h
    · exact h
    · exact absurd ⟨b, hb.1, hb.2, zs, hzs, hmin, h.symm⟩ hcon
  obtain ⟨b1, hb1, hb1f, -⟩ := key 1 one_pos
  have hSne : S.Nonempty := ⟨b1, by simp [S, hb1, hb1f]⟩
  set δ := S.inf' hSne (fun b => c ⬝ᵥ zs - πb b ⬝ᵥ r) with hδ
  have hδpos : 0 < δ := by
    rw [hδ, Finset.lt_inf'_iff]
    intro b hb; linarith [hlt b hb]
  obtain ⟨b, hb, hbf, hbr⟩ := key δ hδpos
  have hbS : b ∈ S := by simp [S, hb, hbf]
  have := Finset.inf'_le (fun b => c ⬝ᵥ zs - πb b ⬝ᵥ r) hbS
  rw [← hδ] at this
  linarith


lemma extend_tight {m : ℕ} (M : Matrix (Fin m) ι ℝ) (c : ι → ℝ) (π : Fin m → ℝ)
    (hspan : Submodule.span ℝ (Set.range (fun j : tight M c π => Mᵀ (j : ι))) = ⊤) :
    ∀ n, ∀ S : Finset ι, m - S.card = n → S ⊆ tight M c π → ColLI M S →
      ∃ S', S ⊆ S' ∧ S' ⊆ tight M c π ∧ ColLI M S' ∧
        Submodule.span ℝ (Set.range (fun j : S' => Mᵀ (j : ι))) = ⊤ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hn hS hli
  by_cases hsp : Submodule.span ℝ (Set.range (fun j : S => Mᵀ (j : ι))) = ⊤
  · exact ⟨S, subset_rfl, hS, hli, hsp⟩
  obtain ⟨j, hjT, hjn⟩ : ∃ j ∈ tight M c π,
      Mᵀ j ∉ Submodule.span ℝ (Set.range (fun j : S => Mᵀ (j : ι))) := by
    by_contra hcon
    push_neg at hcon
    apply hsp
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro v ⟨⟨j, hj⟩, rfl⟩
    exact hcon j hj
  have hjS : j ∉ S := by
    intro h; exact hjn (Submodule.subset_span ⟨⟨j, h⟩, rfl⟩)
  have hli' : ColLI M (insert j S) := by
    have h1 : LinearIndepOn ℝ (fun j => Mᵀ j) (S : Set ι) := hli
    have h2 := h1.insert (x := j) (by
      rw [Set.image_eq_range]; exact hjn)
    show LinearIndepOn ℝ (fun j => Mᵀ j) ((insert j S : Finset ι) : Set ι)
    rw [Finset.coe_insert]
    exact h2
  have hcard : (insert j S).card ≤ m := by
    have := hli'.fintype_card_le_finrank
    simp only [Fintype.card_coe, Module.finrank_fin_fun] at this
    exact this
  rw [Finset.card_insert_of_notMem hjS] at hcard
  obtain ⟨S', h1, h2, h3, h4⟩ := ih (m - (insert j S).card) (by
    rw [Finset.card_insert_of_notMem hjS]; omega) (insert j S) rfl
    (Finset.insert_subset hjT hS) hli'
  exact ⟨S', (Finset.subset_insert _ _).trans h1, h2, h3, h4⟩

theorem opt_basis {m : ℕ} (M : Matrix (Fin m) ι ℝ) (hrow : ∀ d, d ᵥ* M = 0 → d = 0)
    (r : Fin m → ℝ) (c : ι → ℝ) (L : ℝ) (hL : ∀ z, PFeas M r z → L ≤ c ⬝ᵥ z)
    (z0 : ι → ℝ) (hz0 : PFeas M r z0) :
    ∃ b : Fin m → ι, Function.Injective b ∧ IsUnit (M.submatrix id b).det ∧
      (∀ j, 0 ≤ ((M.submatrix id b)⁻¹ *ᵥ r) j) ∧
      (∀ j, ((((M.submatrix id b)ᵀ)⁻¹ *ᵥ (fun i => c (b i))) ᵥ* M) j ≤ c j) ∧
      ∃ zs, PFeas M r zs ∧ (∀ z, PFeas M r z → c ⬝ᵥ zs ≤ c ⬝ᵥ z) ∧
        c ⬝ᵥ zs = (((M.submatrix id b)ᵀ)⁻¹ *ᵥ (fun i => c (b i))) ⬝ᵥ r := by
  classical
  obtain ⟨zs, hzs, hli, hmin⟩ := attain M r c L hL z0 hz0
  obtain ⟨b0, -, hd0, zs0, hzs0, hmin0, heq0⟩ := lpb M hrow r c L hL z0 hz0
  have hcz : c ⬝ᵥ zs0 = c ⬝ᵥ zs := le_antisymm (hmin0 zs hzs) (hmin zs0 hzs0)
  obtain ⟨π', hπ', hle, hspan⟩ := vertex M hrow r c zs hzs _ _ rfl hd0
  have hπr : π' ⬝ᵥ r = c ⬝ᵥ zs :=
    le_antisymm (weak_dual M r c π' hπ' zs hzs) (by rw [← hcz, heq0]; exact hle)
  have hcs : supp zs ⊆ tight M c π' := by
    have hsum : ∑ j, (c j - (π' ᵥ* M) j) * zs j = 0 := by
      have : ∑ j, (c j - (π' ᵥ* M) j) * zs j = c ⬝ᵥ zs - (π' ᵥ* M) ⬝ᵥ zs := by
        simp only [dotProduct, ← Finset.sum_sub_distrib, sub_mul]
      rw [this, ← dotProduct_mulVec, hzs.2, hπr, sub_self]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      mul_nonneg (sub_nonneg.mpr (hπ' j)) (hzs.1 j))).mp hsum
    intro j hj
    rw [mem_supp] at hj
    have := hz j (Finset.mem_univ _)
    rcases mul_eq_zero.mp this with h | h
    · simp [tight]; linarith
    · exact absurd h hj
  obtain ⟨S', hS1, hS2, hS3, hS4⟩ := extend_tight M c π' hspan _ (supp zs) rfl hcs hli
  let B := Module.Basis.mk hS3 (by rw [hS4])
  have hcard : Fintype.card S' = m := by
    have := Module.finrank_eq_card_basis B
    simpa using this.symm
  let e : Fin m ≃ S' := (Fintype.equivFinOfCardEq hcard).symm
  let b : Fin m → ι := fun i => ((e i) : ι)
  have hb : Function.Injective b := by
    intro i1 i2 h
    exact e.injective (Subtype.ext h)
  have hunit : IsUnit (M.submatrix id b) := by
    rw [← linearIndependent_cols_iff_isUnit]
    have := hS3.comp e e.injective
    have heq : (M.submatrix id b).col = ((fun j : S' => Mᵀ (j : ι))) ∘ e := by
      funext i k; simp [b, Matrix.col]
    rw [heq]; exact this
  have hU0 : IsUnit (M.submatrix id b).det := (isUnit_iff_isUnit_det _).mp hunit
  have htb : ∀ i, (π' ᵥ* M) (b i) = c (b i) := by
    intro i
    have := hS2 (e i).2
    simpa [tight] using this
  have hU : IsUnit ((M.submatrix id b)ᵀ).det := by
    rw [det_transpose]; exact hU0
  have hv : (M.submatrix id b)ᵀ *ᵥ π' = fun i => c (b i) := by
    funext i
    rw [← htb i]
    simp [vecMul, mulVec, dotProduct, mul_comm]
  have hπeq : π' = ((M.submatrix id b)ᵀ)⁻¹ *ᵥ (fun i => c (b i)) := by
    rw [← hv, mulVec_mulVec, nonsing_inv_mul _ hU, one_mulVec]
  have hprim : M.submatrix id b *ᵥ (fun i => zs (b i)) = r := by
    rw [← hzs.2, ← sum_sub_eq_mulVec M S' zs (fun j hj => by
      by_contra h; exact hj (hS1 ((mem_supp).mpr h)))]
    funext k
    simp only [mulVec, dotProduct, submatrix_apply, id, Finset.sum_apply, Pi.smul_apply,
      transpose_apply, smul_eq_mul]
    exact Fintype.sum_equiv e _ _ (fun i => by simp only [b]; ring)
  refine ⟨b, hb, hU0, ?_, ?_, zs, hzs, hmin, ?_⟩
  · intro j
    rw [← hprim, mulVec_mulVec, nonsing_inv_mul _ hU0, one_mulVec]
    exact hzs.1 _
  · rw [← hπeq]; exact hπ'
  · rw [← hπeq, hπr]

end LPB
end LPBsec


section Layer
open Matrix LPB Classical

attribute [local instance] Matrix.normedAddCommGroup

variable {m p : ℕ}

/-- basis index -/
abbrev BIdx (m p : ℕ) := Fin m → Fin p

noncomputable def piB (W : Matrix (Fin m) (Fin p) ℝ) (b : BIdx m p) (q : Fin p → ℝ) : Fin m → ℝ :=
  ((W.submatrix id b)ᵀ)⁻¹ *ᵥ (fun i => q (b i))

def DF (W : Matrix (Fin m) (Fin p) ℝ) (b : BIdx m p) (q : Fin p → ℝ) : Prop :=
  ∀ j, (piB W b q ᵥ* W) j ≤ q j

def Good (W : Matrix (Fin m) (Fin p) ℝ) (q : Fin p → ℝ) : Prop := ∃ b, DF W b q

def act (W : Matrix (Fin m) (Fin p) ℝ) (b : BIdx m p) (q : Fin p → ℝ) (r : Fin m → ℝ) : Prop :=
  DF W b q ∧ ∀ b', DF W b' q → piB W b' q ⬝ᵥ r ≤ piB W b q ⬝ᵥ r

noncomputable def ind (W : Matrix (Fin m) (Fin p) ℝ) (b : BIdx m p) (q : Fin p → ℝ)
    (r : Fin m → ℝ) : ℝ := if act W b q r then 1 else 0

noncomputable def cnt (W : Matrix (Fin m) (Fin p) ℝ) (q : Fin p → ℝ) (r : Fin m → ℝ) : ℝ :=
  ∑ b, ind W b q r

noncomputable def Pi (W : Matrix (Fin m) (Fin p) ℝ) (q : Fin p → ℝ) (r : Fin m → ℝ) :
    Fin m → ℝ :=
  (cnt W q r)⁻¹ • ∑ b, ind W b q r • piB W b q

noncomputable def psi (W : Matrix (Fin m) (Fin p) ℝ) (q : Fin p → ℝ) (r : Fin m → ℝ) : ℝ :=
  Pi W q r ⬝ᵥ r

lemma continuous_piB (W : Matrix (Fin m) (Fin p) ℝ) (b : BIdx m p) :
    Continuous fun q => piB W b q :=
  continuous_const.matrix_mulVec (continuous_pi fun i => continuous_apply (b i))

lemma weak {W : Matrix (Fin m) (Fin p) ℝ} {b : BIdx m p} {q : Fin p → ℝ} (hb : DF W b q)
    {r : Fin m → ℝ} {z : Fin p → ℝ} (hz : PFeas W r z) : piB W b q ⬝ᵥ r ≤ q ⬝ᵥ z :=
  weak_dual W r q _ hb z hz

lemma LPValue_ge {W : Matrix (Fin m) (Fin p) ℝ} {b : BIdx m p} {q : Fin p → ℝ} (hb : DF W b q)
    (r : Fin m → ℝ) :
    ((piB W b q ⬝ᵥ r : ℝ) : EReal) ≤ KallMayer.Recourse.LPValue W q r := by
  unfold KallMayer.Recourse.LPValue
  refine le_sInf ?_
  rintro _ ⟨z, hz0, hzW, rfl⟩
  exact EReal.coe_le_coe_iff.2 (weak hb ⟨hz0, hzW⟩)

lemma LPValue_lt_top_iff (W : Matrix (Fin m) (Fin p) ℝ) (q : Fin p → ℝ) (r : Fin m → ℝ) :
    KallMayer.Recourse.LPValue W q r < ⊤ ↔ ∃ z, PFeas W r z := by
  unfold KallMayer.Recourse.LPValue
  rw [sInf_lt_iff]
  constructor
  · rintro ⟨_, ⟨z, hz0, hzW, rfl⟩, _⟩
    exact ⟨z, hz0, hzW⟩
  · rintro ⟨z, hz0, hzW⟩
    exact ⟨_, ⟨z, hz0, hzW, rfl⟩, EReal.coe_lt_top _⟩

lemma exists_act {W : Matrix (Fin m) (Fin p) ℝ} {q : Fin p → ℝ} (hg : Good W q) (r : Fin m → ℝ) :
    ∃ b, act W b q r := by
  obtain ⟨b0, hb0⟩ := hg
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun b => DF W b q)
    (fun b => piB W b q ⬝ᵥ r) ⟨b0, by simpa using hb0⟩
  refine ⟨b, by simpa using hb, fun b' hb' => hmax b' (by simpa using hb')⟩

lemma act_val {W : Matrix (Fin m) (Fin p) ℝ} {q : Fin p → ℝ} {r : Fin m → ℝ} {b b' : BIdx m p}
    (ha : act W b q r) (ha' : act W b' q r) : piB W b q ⬝ᵥ r = piB W b' q ⬝ᵥ r :=
  le_antisymm (ha'.2 b ha.1) (ha.2 b' ha'.1)

lemma ind_nonneg (W : Matrix (Fin m) (Fin p) ℝ) (b : BIdx m p) (q : Fin p → ℝ) (r : Fin m → ℝ) :
    0 ≤ ind W b q r := by
  unfold ind; split_ifs <;> norm_num

lemma ind_le_one (W : Matrix (Fin m) (Fin p) ℝ) (b : BIdx m p) (q : Fin p → ℝ) (r : Fin m → ℝ) :
    ind W b q r ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

lemma cnt_nonneg (W : Matrix (Fin m) (Fin p) ℝ) (q : Fin p → ℝ) (r : Fin m → ℝ) :
    0 ≤ cnt W q r :=
  Finset.sum_nonneg fun b _ => ind_nonneg W b q r

lemma cnt_pos {W : Matrix (Fin m) (Fin p) ℝ} {q : Fin p → ℝ} {r : Fin m → ℝ} {b : BIdx m p}
    (ha : act W b q r) : 0 < cnt W q r := by
  have h1 : ind W b q r = 1 := by simp [ind, ha]
  have := Finset.single_le_sum (f := fun b => ind W b q r) (fun b _ => ind_nonneg W b q r)
    (Finset.mem_univ b)
  unfold cnt; linarith

lemma psi_eq {W : Matrix (Fin m) (Fin p) ℝ} {q : Fin p → ℝ} {r : Fin m → ℝ} {b : BIdx m p}
    (ha : act W b q r) : psi W q r = piB W b q ⬝ᵥ r := by
  have hc := cnt_pos ha
  have hsum : ∑ b', ind W b' q r • piB W b' q ⬝ᵥ r = cnt W q r * (piB W b q ⬝ᵥ r) := by
    unfold cnt
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [smul_dotProduct, smul_eq_mul]
    by_cases h : act W b' q r
    · rw [act_val ha h]
    · simp [ind, h]
  unfold psi Pi
  rw [smul_dotProduct, sum_dotProduct, hsum, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc.ne',
    one_mul]

lemma Pi_eq {W : Matrix (Fin m) (Fin p) ℝ} {q : Fin p → ℝ} {r : Fin m → ℝ} {b : BIdx m p}
    (ha : act W b q r) (huniq : ∀ b', act W b' q r → piB W b' q = piB W b q) :
    Pi W q r = piB W b q := by
  have hc := cnt_pos ha
  have hsum : ∑ b', ind W b' q r • piB W b' q = cnt W q r • piB W b q := by
    unfold cnt
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun b' _ => ?_
    by_cases h : act W b' q r
    · rw [huniq b' h]
    · simp [ind, h]
  unfold Pi
  rw [hsum, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

lemma psi_ge {W : Matrix (Fin m) (Fin p) ℝ} {q : Fin p → ℝ} {b : BIdx m p} (hb : DF W b q)
    (r : Fin m → ℝ) : piB W b q ⬝ᵥ r ≤ psi W q r := by
  obtain ⟨b', hb'⟩ := exists_act ⟨b, hb⟩ r
  rw [psi_eq hb']
  exact hb'.2 b hb

lemma Pi_eq_zero {W : Matrix (Fin m) (Fin p) ℝ} {q : Fin p → ℝ} (hg : ¬ Good W q) (r : Fin m → ℝ) :
    Pi W q r = 0 := by
  have : ∀ b, ind W b q r = 0 := by
    intro b
    have : ¬ act W b q r := fun h => hg ⟨b, h.1⟩
    simp [ind, this]
  unfold Pi
  simp [this]

lemma psi_eq_zero {W : Matrix (Fin m) (Fin p) ℝ} {q : Fin p → ℝ} (hg : ¬ Good W q) (r : Fin m → ℝ) :
    psi W q r = 0 := by
  unfold psi; rw [Pi_eq_zero hg]; simp

/-- Strong-duality representation of the LP value, given full row rank. -/
lemma LPValue_eq_psi {W : Matrix (Fin m) (Fin p) ℝ} (hrow : ∀ d, d ᵥ* W = 0 → d = 0)
    {q : Fin p → ℝ} {r : Fin m → ℝ} (hfeas : ∃ z, PFeas W r z)
    (hbot : KallMayer.Recourse.LPValue W q r ≠ ⊥) :
    Good W q ∧ KallMayer.Recourse.LPValue W q r = ((psi W q r : ℝ) : EReal) := by
  obtain ⟨z0, hz0⟩ := hfeas
  have hlt : KallMayer.Recourse.LPValue W q r < ⊤ := (LPValue_lt_top_iff W q r).2 ⟨z0, hz0⟩
  set v := (KallMayer.Recourse.LPValue W q r).toReal with hv
  have hvv : ((v : ℝ) : EReal) = KallMayer.Recourse.LPValue W q r := EReal.coe_toReal hlt.ne hbot
  have hL : ∀ z, PFeas W r z → v ≤ q ⬝ᵥ z := by
    intro z hz
    have : KallMayer.Recourse.LPValue W q r ≤ ((q ⬝ᵥ z : ℝ) : EReal) := by
      unfold KallMayer.Recourse.LPValue
      exact sInf_le ⟨z, hz.1, hz.2, rfl⟩
    rw [← hvv] at this
    exact EReal.coe_le_coe_iff.1 this
  obtain ⟨b, -, -, -, hdual, zs, hzs, hmin, heq⟩ := opt_basis W hrow r q v hL z0 hz0
  have hb : DF W b q := hdual
  have heq' : q ⬝ᵥ zs = piB W b q ⬝ᵥ r := heq
  have hval : KallMayer.Recourse.LPValue W q r = ((q ⬝ᵥ zs : ℝ) : EReal) := by
    apply le_antisymm
    · unfold KallMayer.Recourse.LPValue
      exact sInf_le ⟨zs, hzs.1, hzs.2, rfl⟩
    · unfold KallMayer.Recourse.LPValue
      refine le_sInf ?_
      rintro _ ⟨z, hz0', hzW, rfl⟩
      exact EReal.coe_le_coe_iff.2 (hmin z ⟨hz0', hzW⟩)
  have hact : act W b q r := by
    refine ⟨hb, fun b' hb' => ?_⟩
    have := LPValue_ge hb' r
    rw [hval] at this
    have := EReal.coe_le_coe_iff.1 this
    change piB W b' q ⬝ᵥ r ≤ piB W b q ⬝ᵥ r
    linarith [heq']
  refine ⟨⟨b, hb⟩, ?_⟩
  rw [hval, psi_eq hact, heq']

/-- Abs-dot bound. -/
lemma abs_dot_le {k : ℕ} (w y : Fin k → ℝ) : |w ⬝ᵥ y| ≤ ‖w‖ * ∑ j, |y j| := by
  unfold dotProduct
  calc |∑ j, w j * y j| ≤ ∑ j, |w j * y j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ‖w‖ * |y j| := by
        apply Finset.sum_le_sum; intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right
          (by simpa [Real.norm_eq_abs] using norm_le_pi_norm w j) (abs_nonneg _)
    _ = ‖w‖ * ∑ j, |y j| := by rw [Finset.mul_sum]

lemma sum_abs_le_norm {k : ℕ} (v : Fin k → ℝ) : ∑ j, |v j| ≤ (k : ℝ) * ‖v‖ := by
  calc ∑ j, |v j| ≤ ∑ _j : Fin k, ‖v‖ := Finset.sum_le_sum fun j _ => by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm v j
    _ = (k : ℝ) * ‖v‖ := by simp

lemma norm_mulVec_bound {k l : ℕ} (M : Matrix (Fin k) (Fin l) ℝ) (v : Fin l → ℝ) :
    ‖M *ᵥ v‖ ≤ ‖M‖ * ∑ j, |v j| := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  calc |(M *ᵥ v) i| = |M i ⬝ᵥ v| := rfl
    _ ≤ ‖M i‖ * ∑ j, |v j| := abs_dot_le _ _
    _ ≤ ‖M‖ * ∑ j, |v j| :=
        mul_le_mul_of_nonneg_right (norm_le_pi_norm M i) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- A uniform constant bounding all `piB`. -/
lemma piB_bound (W : Matrix (Fin m) (Fin p) ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b q, ‖piB W b q‖ ≤ C * ‖q‖ := by
  refine ⟨∑ b : BIdx m p, (m : ℝ) * ‖((W.submatrix id b)ᵀ)⁻¹‖, by positivity, fun b q => ?_⟩
  have h1 : ‖piB W b q‖ ≤ ‖((W.submatrix id b)ᵀ)⁻¹‖ * ∑ i, |q (b i)| := norm_mulVec_bound _ _
  have h2 : ∑ i, |q (b i)| ≤ (m : ℝ) * ‖q‖ := by
    calc ∑ i, |q (b i)| ≤ ∑ _i : Fin m, ‖q‖ := Finset.sum_le_sum fun i _ => by
          simpa [Real.norm_eq_abs] using norm_le_pi_norm q (b i)
      _ = (m : ℝ) * ‖q‖ := by simp
  have h3 : (m : ℝ) * ‖((W.submatrix id b)ᵀ)⁻¹‖ ≤
      ∑ b : BIdx m p, (m : ℝ) * ‖((W.submatrix id b)ᵀ)⁻¹‖ :=
    Finset.single_le_sum (f := fun b => (m : ℝ) * ‖((W.submatrix id b)ᵀ)⁻¹‖)
      (fun _ _ => by positivity) (Finset.mem_univ b)
  have hq : 0 ≤ ‖q‖ := norm_nonneg _
  have hM : 0 ≤ ‖((W.submatrix id b)ᵀ)⁻¹‖ := norm_nonneg _
  calc ‖piB W b q‖ ≤ ‖((W.submatrix id b)ᵀ)⁻¹‖ * ((m : ℝ) * ‖q‖) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 hM)
    _ = ((m : ℝ) * ‖((W.submatrix id b)ᵀ)⁻¹‖) * ‖q‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h3 hq

lemma Pi_bound {W : Matrix (Fin m) (Fin p) ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ b q, ‖piB W b q‖ ≤ C * ‖q‖) (q : Fin p → ℝ) (r : Fin m → ℝ) :
    ‖Pi W q r‖ ≤ C * ‖q‖ := by
  by_cases hg : Good W q
  · obtain ⟨b, hb⟩ := exists_act hg r
    have hc := cnt_pos hb
    have hCq : 0 ≤ C * ‖q‖ := by positivity
    refine (pi_norm_le_iff_of_nonneg hCq).2 fun i => ?_
    unfold Pi
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Real.norm_eq_abs]
    have hS : |∑ b', ind W b' q r * piB W b' q i| ≤ cnt W q r * (C * ‖q‖) := by
      unfold cnt
      rw [Finset.sum_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b' _ => ?_)
      rw [abs_mul, abs_of_nonneg (ind_nonneg _ _ _ _)]
      refine mul_le_mul_of_nonneg_left ?_ (ind_nonneg _ _ _ _)
      have := norm_le_pi_norm (piB W b' q) i
      rw [Real.norm_eq_abs] at this
      exact this.trans (hC b' q)
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 hc.le)]
    calc (cnt W q r)⁻¹ * |∑ b', ind W b' q r * piB W b' q i|
        ≤ (cnt W q r)⁻¹ * (cnt W q r * (C * ‖q‖)) :=
          mul_le_mul_of_nonneg_left hS (inv_nonneg.2 hc.le)
      _ = C * ‖q‖ := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  · rw [Pi_eq_zero hg]; simp; positivity

lemma psi_bound {W : Matrix (Fin m) (Fin p) ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ b q, ‖piB W b q‖ ≤ C * ‖q‖) (q : Fin p → ℝ) (r : Fin m → ℝ) :
    |psi W q r| ≤ C * ‖q‖ * ∑ i, |r i| := by
  unfold psi
  refine (abs_dot_le _ _).trans ?_
  exact mul_le_mul_of_nonneg_right (Pi_bound hC0 hC q r) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

lemma psi_lip {W : Matrix (Fin m) (Fin p) ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ b q, ‖piB W b q‖ ≤ C * ‖q‖) (q : Fin p → ℝ) (r r' : Fin m → ℝ) :
    |psi W q r - psi W q r'| ≤ C * ‖q‖ * ∑ i, |(r - r') i| := by
  by_cases hg : Good W q
  · have key : ∀ s s' : Fin m → ℝ, psi W q s - psi W q s' ≤ C * ‖q‖ * ∑ i, |(s - s') i| := by
      intro s s'
      obtain ⟨b, hb⟩ := exists_act hg s
      have h1 := psi_ge hb.1 s'
      rw [psi_eq hb]
      have h2 : piB W b q ⬝ᵥ s - piB W b q ⬝ᵥ s' = piB W b q ⬝ᵥ (s - s') := by
        rw [dotProduct_sub]
      have h3 := abs_dot_le (piB W b q) (s - s')
      have h4 : ‖piB W b q‖ * ∑ i, |(s - s') i| ≤ C * ‖q‖ * ∑ i, |(s - s') i| :=
        mul_le_mul_of_nonneg_right (hC b q) (Finset.sum_nonneg fun i _ => abs_nonneg _)
      linarith [le_abs_self (piB W b q ⬝ᵥ (s - s'))]
    rw [abs_sub_le_iff]
    refine ⟨key r r', ?_⟩
    have := key r' r
    have hsym : ∑ i, |(r' - r) i| = ∑ i, |(r - r') i| := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.sub_apply, Pi.sub_apply, abs_sub_comm]
    rw [hsym] at this
    exact this
  · rw [psi_eq_zero hg, psi_eq_zero hg]; simp; positivity

/-- local linearity at a point where all maximisers share the same dual vector -/
lemma eventually_linear {W : Matrix (Fin m) (Fin p) ℝ} {q : Fin p → ℝ} (hg : Good W q)
    (r0 : Fin m → ℝ)
    (huniq : ∀ b b', act W b q r0 → act W b' q r0 → piB W b' q = piB W b q) :
    ∀ᶠ r in nhds r0, Pi W q r = Pi W q r0 ∧ psi W q r = Pi W q r0 ⬝ᵥ r := by
  obtain ⟨b0, hb0⟩ := exists_act hg r0
  have hP0 : Pi W q r0 = piB W b0 q := Pi_eq hb0 (fun b' h => huniq b0 b' hb0 h)
  have hev : ∀ᶠ r in nhds r0, ∀ b', (DF W b' q ∧ ¬ act W b' q r0) →
      piB W b' q ⬝ᵥ r < piB W b0 q ⬝ᵥ r := by
    rw [Filter.eventually_all]
    intro b'
    by_cases h : DF W b' q ∧ ¬ act W b' q r0
    · have hlt : piB W b' q ⬝ᵥ r0 < piB W b0 q ⬝ᵥ r0 := by
        by_contra hge
        push Not at hge
        apply h.2
        refine ⟨h.1, fun b'' hb'' => ?_⟩
        exact (hb0.2 b'' hb'').trans hge
      have hc1 : Continuous fun r : Fin m → ℝ => piB W b' q ⬝ᵥ r :=
        continuous_const.dotProduct continuous_id
      have hc2 : Continuous fun r : Fin m → ℝ => piB W b0 q ⬝ᵥ r :=
        continuous_const.dotProduct continuous_id
      have := (hc1.continuousAt (x := r0)).eventually_lt (hc2.continuousAt) hlt
      exact this.mono fun r hr _ => hr
    · exact Filter.Eventually.of_forall fun r hr => absurd hr h
  refine hev.mono fun r hr => ?_
  have hall : ∀ b, act W b q r → piB W b q = piB W b0 q := by
    intro b hb
    by_cases hb' : act W b q r0
    · exact huniq b0 b hb0 hb'
    · exfalso
      have h1 := hr b ⟨hb.1, hb'⟩
      have h2 := hb.2 b0 hb0.1
      linarith
  obtain ⟨b1, hb1⟩ := exists_act hg r
  refine ⟨?_, ?_⟩
  · rw [Pi_eq hb1 (fun b' h => (hall b' h).trans (hall b1 hb1).symm), hall b1 hb1, hP0]
  · rw [psi_eq hb1, hall b1 hb1, hP0]

end Layer


section Part2
open Matrix LPB Classical

attribute [local instance] Matrix.normedAddCommGroup

variable {m n p : ℕ}

/-- dual feasible set -/
def Dset (W : Matrix (Fin m) (Fin p) ℝ) : Set (Fin p → ℝ) :=
  {q | ∃ z : Fin m → ℝ, ∀ j, (z ᵥ* W) j ≤ q j}

/-- The matrix `[Wᵀ | -Wᵀ | I]`. -/
def Mdual (W : Matrix (Fin m) (Fin p) ℝ) : Matrix (Fin p) (Fin m ⊕ Fin m ⊕ Fin p) ℝ :=
  fun j k => Sum.elim (fun i => W i j)
    (Sum.elim (fun i => -W i j) (fun j' => if j = j' then 1 else 0)) k

lemma Mdual_mulVec (W : Matrix (Fin m) (Fin p) ℝ) (w : Fin m ⊕ Fin m ⊕ Fin p → ℝ) (j : Fin p) :
    (Mdual W *ᵥ w) j =
      ((fun i => w (Sum.inl i) - w (Sum.inr (Sum.inl i))) ᵥ* W) j + w (Sum.inr (Sum.inr j)) := by
  simp only [mulVec, dotProduct, vecMul, Mdual, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  have : ∀ i, -W i j * w (Sum.inr (Sum.inl i)) = -(w (Sum.inr (Sum.inl i)) * W i j) := fun i => by ring
  simp only [this, Finset.sum_neg_distrib]
  have h2 : ∀ i, W i j * w (Sum.inl i) = w (Sum.inl i) * W i j := fun i => by ring
  simp only [h2]
  ring

lemma vecMul_Mdual (W : Matrix (Fin m) (Fin p) ℝ) (y : Fin p → ℝ) :
    (∀ i, (y ᵥ* Mdual W) (Sum.inl i) = (W *ᵥ y) i) ∧
    (∀ i, (y ᵥ* Mdual W) (Sum.inr (Sum.inl i)) = -(W *ᵥ y) i) ∧
    (∀ j, (y ᵥ* Mdual W) (Sum.inr (Sum.inr j)) = y j) := by
  refine ⟨fun i => ?_, fun i => ?_, fun j => ?_⟩
  · simp [vecMul, mulVec, dotProduct, Mdual, mul_comm]
  · simp [vecMul, mulVec, dotProduct, Mdual, mul_comm, Finset.sum_neg_distrib]
  · simp [vecMul, dotProduct, Mdual]

lemma Dset_eq_cone (W : Matrix (Fin m) (Fin p) ℝ) : Dset W = cone (Mdual W) := by
  ext q
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨Sum.elim (fun i => max (z i) 0)
      (Sum.elim (fun i => max (-z i) 0) (fun j => q j - (z ᵥ* W) j)), ?_, ?_⟩
    · intro k
      rcases k with i | i | j
      · exact le_max_right _ _
      · exact le_max_right _ _
      · simp only [Sum.elim_inr]; linarith [hz j]
    · funext j
      rw [mulVecLin_apply, Mdual_mulVec]
      simp only [Sum.elim_inl, Sum.elim_inr, max_zero_sub_max_neg_zero_eq_self]
      ring
  · rintro ⟨w, hw, hwq⟩
    refine ⟨fun i => w (Sum.inl i) - w (Sum.inr (Sum.inl i)), fun j => ?_⟩
    have := congrFun hwq j
    rw [mulVecLin_apply, Mdual_mulVec] at this
    have h0 := hw (Sum.inr (Sum.inr j))
    linarith

lemma Dset_closed (W : Matrix (Fin m) (Fin p) ℝ) : IsClosed (Dset W) := by
  rw [Dset_eq_cone]; exact cone_closed _

lemma farkas_D {W : Matrix (Fin m) (Fin p) ℝ} {q : Fin p → ℝ} (hq : q ∉ Dset W) :
    ∃ y : Fin p → ℝ, (∀ j, 0 ≤ y j) ∧ W *ᵥ y = 0 ∧ q ⬝ᵥ y < 0 := by
  rw [Dset_eq_cone] at hq
  obtain ⟨y, hy, hyq⟩ := farkas (Mdual W) q hq
  obtain ⟨h1, h2, h3⟩ := vecMul_Mdual W y
  refine ⟨y, fun j => by rw [← h3 j]; exact hy _, ?_, by rwa [dotProduct_comm]⟩
  funext i
  have a := hy (Sum.inl i)
  have b := hy (Sum.inr (Sum.inl i))
  rw [h1] at a; rw [h2] at b
  simp only [Pi.zero_apply]; linarith

lemma LPValue_eq_bot {W : Matrix (Fin m) (Fin p) ℝ} {q : Fin p → ℝ} {r : Fin m → ℝ}
    (hfeas : ∃ z, PFeas W r z) (y : Fin p → ℝ) (hy0 : ∀ j, 0 ≤ y j) (hyW : W *ᵥ y = 0)
    (hyq : q ⬝ᵥ y < 0) : KallMayer.Recourse.LPValue W q r = ⊥ := by
  obtain ⟨y0, hy00, hy0W⟩ := hfeas
  rw [EReal.eq_bot_iff_forall_lt]
  intro s
  set t : ℝ := (|q ⬝ᵥ y0 - s| + 1) / (-(q ⬝ᵥ y)) with ht
  have hpos : 0 < -(q ⬝ᵥ y) := by linarith
  have ht0 : 0 ≤ t := by positivity
  have htc : t * (q ⬝ᵥ y) = -(|q ⬝ᵥ y0 - s| + 1) := by
    have hne : q ⬝ᵥ y ≠ 0 := hyq.ne
    rw [ht, div_mul_eq_mul_div, div_neg, mul_div_assoc, div_self hne, mul_one]
  unfold KallMayer.Recourse.LPValue
  refine lt_of_le_of_lt (sInf_le ⟨y0 + t • y, fun j => ?_, ?_, rfl⟩) ?_
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (hy00 j) (mul_nonneg ht0 (hy0 j))
  · rw [mulVec_add, mulVec_smul, hyW, hy0W, smul_zero, add_zero]
  · refine EReal.coe_lt_coe_iff.2 ?_
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul, htc]
    have := le_abs_self (q ⬝ᵥ y0 - s)
    linarith

lemma LPValue_ne_bot_of_D {W : Matrix (Fin m) (Fin p) ℝ} {q : Fin p → ℝ} (hq : q ∈ Dset W)
    (r : Fin m → ℝ) : KallMayer.Recourse.LPValue W q r ≠ ⊥ := by
  obtain ⟨z, hz⟩ := hq
  have : ((z ⬝ᵥ r : ℝ) : EReal) ≤ KallMayer.Recourse.LPValue W q r := by
    unfold KallMayer.Recourse.LPValue
    refine le_sInf ?_
    rintro _ ⟨y, hy0, hyW, rfl⟩
    exact EReal.coe_le_coe_iff.2 (weak_dual W r q z hz y ⟨hy0, hyW⟩)
  intro h
  rw [h] at this
  exact absurd this (by simp)

/-! ### Continuity / measurability in the data -/

lemma continuous_rf (x : Fin n → ℝ) :
    Continuous fun ξ : RecourseData m n p => ξ.2.1 - ξ.1 *ᵥ x := by
  have h1 : Continuous fun ξ : RecourseData m n p => ξ.2.1 := continuous_fst.comp continuous_snd
  have h2 : Continuous fun ξ : RecourseData m n p => (ξ.1 : Matrix (Fin m) (Fin n) ℝ) *ᵥ x :=
    continuous_fst.matrix_mulVec continuous_const
  exact h1.sub h2

lemma continuous_qf : Continuous fun ξ : RecourseData m n p => ξ.2.2 :=
  continuous_snd.comp continuous_snd

lemma measurableSet_DF (W : Matrix (Fin m) (Fin p) ℝ) (b : BIdx m p) :
    MeasurableSet {ξ : RecourseData m n p | DF W b ξ.2.2} := by
  have : {ξ : RecourseData m n p | DF W b ξ.2.2} =
      ⋂ j, {ξ | (piB W b ξ.2.2 ᵥ* W) j ≤ ξ.2.2 j} := by
    ext ξ; simp [DF]
  rw [this]
  refine MeasurableSet.iInter fun j => (isClosed_le ?_ ?_).measurableSet
  · exact (continuous_apply j).comp
      (((continuous_piB W b).comp continuous_qf).matrix_vecMul continuous_const)
  · exact (continuous_apply j).comp continuous_qf

lemma measurableSet_act (W : Matrix (Fin m) (Fin p) ℝ) (x : Fin n → ℝ) (b : BIdx m p) :
    MeasurableSet {ξ : RecourseData m n p | act W b ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x)} := by
  have hc : ∀ b', Continuous fun ξ : RecourseData m n p =>
      piB W b' ξ.2.2 ⬝ᵥ (ξ.2.1 - ξ.1 *ᵥ x) :=
    fun b' => ((continuous_piB W b').comp continuous_qf).dotProduct (continuous_rf x)
  have : {ξ : RecourseData m n p | act W b ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x)} =
      {ξ | DF W b ξ.2.2} ∩ ⋂ b', ({ξ | DF W b' ξ.2.2}ᶜ ∪
        {ξ | piB W b' ξ.2.2 ⬝ᵥ (ξ.2.1 - ξ.1 *ᵥ x) ≤ piB W b ξ.2.2 ⬝ᵥ (ξ.2.1 - ξ.1 *ᵥ x)}) := by
    ext ξ
    simp only [act, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_union,
      Set.mem_compl_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun b' => ?_⟩
      by_cases h : DF W b' ξ.2.2
      · exact Or.inr (h2 b' h)
      · exact Or.inl h
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun b' hb' => ?_⟩
      rcases h2 b' with h | h
      · exact absurd hb' h
      · exact h
  rw [this]
  refine (measurableSet_DF W b).inter (MeasurableSet.iInter fun b' => ?_)
  exact (measurableSet_DF W b').compl.union ((isClosed_le (hc b') (hc b)).measurableSet)

lemma measurable_ind (W : Matrix (Fin m) (Fin p) ℝ) (x : Fin n → ℝ) (b : BIdx m p) :
    Measurable fun ξ : RecourseData m n p => ind W b ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) := by
  unfold ind
  exact Measurable.ite (measurableSet_act W x b) measurable_const measurable_const

lemma measurable_cnt (W : Matrix (Fin m) (Fin p) ℝ) (x : Fin n → ℝ) :
    Measurable fun ξ : RecourseData m n p => cnt W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) := by
  unfold cnt
  exact Finset.measurable_sum _ fun b _ => measurable_ind W x b

lemma Pi_apply (W : Matrix (Fin m) (Fin p) ℝ) (q : Fin p → ℝ) (r : Fin m → ℝ) (i : Fin m) :
    Pi W q r i = (cnt W q r)⁻¹ * ∑ b, ind W b q r * piB W b q i := by
  simp [Pi, Finset.sum_apply]

lemma measurable_Pi (W : Matrix (Fin m) (Fin p) ℝ) (x : Fin n → ℝ) :
    Measurable fun ξ : RecourseData m n p => Pi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) := by
  rw [measurable_pi_iff]
  intro i
  simp only [Pi_apply]
  refine (measurable_cnt W x).inv.mul (Finset.measurable_sum _ fun b _ => ?_)
  exact (measurable_ind W x b).mul
    (((continuous_apply i).comp ((continuous_piB W b).comp continuous_qf)).measurable)

lemma measurable_psi (W : Matrix (Fin m) (Fin p) ℝ) (x : Fin n → ℝ) :
    Measurable fun ξ : RecourseData m n p => psi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) := by
  unfold psi dotProduct
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((measurable_pi_iff.1 (measurable_Pi W x)) i).mul
    (((continuous_apply i).comp (continuous_rf x)).measurable)

/-! ### Null sets -/

lemma slice_null (S : Set (RecourseData m n p)) (hS : MeasurableSet S)
    (h : ∀ (T : Fin m → Fin n → ℝ) (q : Fin p → ℝ),
      volume {h : Fin m → ℝ | (T, (h, q)) ∈ S} = 0) : volume S = 0 := by
  have hT : ∀ T : Fin m → Fin n → ℝ,
      (volume : Measure ((Fin m → ℝ) × (Fin p → ℝ))) (Prod.mk T ⁻¹' S) = 0 := by
    intro T
    rw [Measure.volume_eq_prod, Measure.prod_apply_symm (measurable_prodMk_left hS)]
    have : ∀ q : Fin p → ℝ,
        (volume : Measure (Fin m → ℝ)) ((fun h => (h, q)) ⁻¹' (Prod.mk T ⁻¹' S)) = 0 := by
      intro q
      exact h T q
    simp [this]
  rw [Measure.volume_eq_prod, Measure.prod_apply hS]
  simp [hT]

lemma hyperplane_null (w : Fin m → ℝ) (hw : w ≠ 0) (c : ℝ) :
    volume {h : Fin m → ℝ | w ⬝ᵥ h = c} = 0 := by
  let L : (Fin m → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun h => w ⬝ᵥ h
      map_add' := fun a b => dotProduct_add _ _ _
      map_smul' := fun r a => by simp [dotProduct_smul] }
  have hww : w ⬝ᵥ w ≠ 0 := by
    intro h; exact hw (dotProduct_self_eq_zero.1 h)
  have hker : LinearMap.ker L ≠ ⊤ := by
    intro h
    have : w ∈ LinearMap.ker L := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker] at this
    exact hww this
  have h0 := Measure.addHaar_submodule (volume : Measure (Fin m → ℝ)) (LinearMap.ker L) hker
  set h₀ : Fin m → ℝ := (c / (w ⬝ᵥ w)) • w with hh₀
  have hc : w ⬝ᵥ h₀ = c := by
    rw [hh₀, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hww]
  have hset : {h : Fin m → ℝ | w ⬝ᵥ h = c} = (fun h => h + (-h₀)) ⁻¹' (LinearMap.ker L : Set _) := by
    ext h
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, LinearMap.mem_ker]
    change w ⬝ᵥ h = c ↔ w ⬝ᵥ (h + -h₀) = 0
    rw [dotProduct_add, dotProduct_neg, hc]
    constructor <;> intro h' <;> linarith
  rw [hset, measure_preimage_add_right]
  exact h0

lemma pair_null {μ : Measure (RecourseData m n p)} (hdensity : μ ≪ volume)
    (W : Matrix (Fin m) (Fin p) ℝ) (x : Fin n → ℝ) (b b' : BIdx m p) :
    μ {ξ : RecourseData m n p | piB W b ξ.2.2 ≠ piB W b' ξ.2.2 ∧
      (piB W b ξ.2.2 - piB W b' ξ.2.2) ⬝ᵥ (ξ.2.1 - ξ.1 *ᵥ x) = 0} = 0 := by
  apply hdensity
  apply slice_null
  · refine MeasurableSet.inter ?_ ?_
    · exact (isClosed_eq ((continuous_piB W b).comp continuous_qf)
        ((continuous_piB W b').comp continuous_qf)).isOpen_compl.measurableSet
    · exact (isClosed_eq ((((continuous_piB W b).comp continuous_qf).sub
        ((continuous_piB W b').comp continuous_qf)).dotProduct (continuous_rf x))
        continuous_const).measurableSet
  · intro T q
    by_cases hw : piB W b q = piB W b' q
    · simp [hw]
    · refine measure_mono_null ?_
        (hyperplane_null (piB W b q - piB W b' q) (sub_ne_zero.2 hw)
          ((piB W b q - piB W b' q) ⬝ᵥ (T *ᵥ x)))
      intro h hh
      simp only [Set.mem_ofPred_eq] at hh ⊢
      have := hh.2
      rw [dotProduct_sub, sub_eq_zero] at this
      exact this

lemma hrow_null {μ : Measure (RecourseData m n p)} (hdensity : μ ≪ volume)
    (x : Fin n → ℝ) (d : Fin m → ℝ) (hd : d ≠ 0) :
    μ {ξ : RecourseData m n p | d ⬝ᵥ (ξ.2.1 - ξ.1 *ᵥ x) = 0} = 0 := by
  apply hdensity
  apply slice_null
  · exact (isClosed_eq (continuous_const.dotProduct (continuous_rf x)) continuous_const).measurableSet
  · intro T q
    refine measure_mono_null ?_ (hyperplane_null d hd (d ⬝ᵥ (T *ᵥ x)))
    intro h hh
    simp only [Set.mem_ofPred_eq] at hh ⊢
    rw [dotProduct_sub, sub_eq_zero] at hh
    exact hh

end Part2


section Part3
open Matrix LPB Classical Filter Topology

attribute [local instance] Matrix.normedAddCommGroup

variable {m n p : ℕ}

lemma ae_feas {μ : Measure (RecourseData m n p)} {W : Matrix (Fin m) (Fin p) ℝ} {x : Fin n → ℝ}
    (hx : x ∈ recourseDomain μ W) :
    ∀ᵐ ξ ∂μ, ∃ z, PFeas W (ξ.2.1 - ξ.1 *ᵥ x) z := by
  have hx' : ∀ᵐ ξ ∂μ, KallMayer.Recourse.PointwiseRecourse W ξ.1 ξ.2.1 ξ.2.2 x < ⊤ := hx
  exact hx'.mono fun ξ h => (LPValue_lt_top_iff _ _ _).1 h

lemma integrable_base {μ : Measure (RecourseData m n p)}
    [IsProbabilityMeasure μ] (hmom : recourseMomentAlternative μ) :
    Integrable (fun d : RecourseData m n p => (‖d.1‖ + ‖d.2.1‖) * ‖d.2.2‖) μ := by
  rcases hmom with ⟨h1, h2, h3⟩ | ⟨⟨q0, hq⟩, hA, hb⟩ | ⟨⟨A0, b0, hAb⟩, hq⟩ | ⟨C, hC⟩
  · exact (h1.norm.add h2.norm).integrable_mul h3.norm
  · refine ((hA.norm.add hb.norm).mul_const ‖q0‖).congr (hq.mono fun d hd => ?_)
    simp [hd]
  · refine (hq.norm.const_mul (‖(fun i => A0 i : Fin m → Fin n → ℝ)‖ + ‖b0‖)).congr
      (hAb.mono fun d hd => ?_)
    simp only [hd.1, hd.2]
  · have hcont : Continuous fun d : RecourseData m n p => (‖d.1‖ + ‖d.2.1‖) * ‖d.2.2‖ := by
      fun_prop
    refine Integrable.of_bound hcont.aestronglyMeasurable ((C + C) * C) (hC.mono fun d hd => ?_)
    obtain ⟨ha, hb, hc⟩ := hd
    have h0 : 0 ≤ C := (norm_nonneg _).trans ha
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul (add_le_add ha hb) hc (norm_nonneg _) (by linarith)

lemma ae_D {μ : Measure (RecourseData m n p)} [IsProbabilityMeasure μ]
    {W : Matrix (Fin m) (Fin p) ℝ} {x : Fin n → ℝ}
    (hx : x ∈ recourseDomain μ W) (hb : ⊥ < extendedExpectedRecourse μ W x) :
    ∀ᵐ ξ ∂μ, ξ.2.2 ∈ Dset W := by
  by_contra hcon
  rw [ae_iff] at hcon
  have hfe := ae_feas hx
  rw [ae_iff] at hfe
  set N := {ξ : RecourseData m n p | ¬ ξ.2.2 ∈ Dset W} ∩
    {ξ | ∃ z, PFeas W (ξ.2.1 - ξ.1 *ᵥ x) z} with hN
  have hNm : MeasurableSet N := by
    refine MeasurableSet.inter ?_ ?_
    · exact continuous_qf.measurable (Dset_closed W).isOpen_compl.measurableSet
    · have : {ξ : RecourseData m n p | ∃ z, PFeas W (ξ.2.1 - ξ.1 *ᵥ x) z} =
          (fun ξ : RecourseData m n p => ξ.2.1 - ξ.1 *ᵥ x) ⁻¹' cone W := by
        ext ξ
        constructor
        · rintro ⟨z, hz0, hzW⟩; exact ⟨z, hz0, hzW⟩
        · rintro ⟨z, hz0, hzW⟩; exact ⟨z, hz0, hzW⟩
      rw [this]
      exact (continuous_rf x).measurable (cone_closed W).measurableSet
  have hμN : μ N ≠ 0 := by
    have h := measure_inter_conull (μ := μ) (s := {ξ : RecourseData m n p | ¬ ξ.2.2 ∈ Dset W})
      (t := {ξ : RecourseData m n p | ∃ z, PFeas W (ξ.2.1 - ξ.1 *ᵥ x) z}) hfe
    exact fun h0 => hcon (h.symm.trans h0)
  have hbot : ∀ ξ ∈ N,
      (-KallMayer.Recourse.PointwiseRecourse W ξ.1 ξ.2.1 ξ.2.2 x).toENNReal = ⊤ := by
    intro ξ hξ
    obtain ⟨y, hy0, hyW, hyq⟩ := farkas_D hξ.1
    change (-KallMayer.Recourse.LPValue W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x)).toENNReal = ⊤
    rw [LPValue_eq_bot hξ.2 y hy0 hyW hyq]
    simp
  have htop : ∫⁻ ξ, (-KallMayer.Recourse.PointwiseRecourse W ξ.1 ξ.2.1 ξ.2.2 x).toENNReal ∂μ
      = ⊤ := by
    refine eq_top_iff.2 ?_
    calc (⊤ : ENNReal) = ∫⁻ ξ, N.indicator (fun _ => (⊤ : ENNReal)) ξ ∂μ := by
          rw [lintegral_indicator_const hNm, ENNReal.top_mul hμN]
      _ ≤ _ := lintegral_mono fun ξ => by
          by_cases hξ : ξ ∈ N
          · simp [Set.indicator_of_mem hξ, hbot ξ hξ]
          · simp [Set.indicator_of_notMem hξ]
  unfold extendedExpectedRecourse at hb
  rw [htop, EReal.coe_ennreal_top, EReal.sub_top] at hb
  exact lt_irrefl _ hb

lemma ae_good_eq {μ : Measure (RecourseData m n p)} [IsProbabilityMeasure μ]
    {W : Matrix (Fin m) (Fin p) ℝ} (hrow : ∀ d, d ᵥ* W = 0 → d = 0) {x : Fin n → ℝ}
    (hx : x ∈ recourseDomain μ W) (hb : ⊥ < extendedExpectedRecourse μ W x) :
    ∀ᵐ ξ ∂μ, Good W ξ.2.2 ∧ KallMayer.Recourse.LPValue W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) =
      ((psi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) : ℝ) : EReal) :=
  ((ae_feas hx).and (ae_D hx hb)).mono fun ξ ⟨hf, hD⟩ =>
    LPValue_eq_psi hrow hf (LPValue_ne_bot_of_D hD _)

lemma ae_uniq {μ : Measure (RecourseData m n p)} (hdensity : μ ≪ volume)
    (W : Matrix (Fin m) (Fin p) ℝ) (x : Fin n → ℝ) :
    ∀ᵐ ξ ∂μ, ∀ b b', act W b ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) → act W b' ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) →
      piB W b' ξ.2.2 = piB W b ξ.2.2 := by
  rw [ae_all_iff]; intro b; rw [ae_all_iff]; intro b'
  rw [ae_iff]
  refine measure_mono_null ?_ (pair_null hdensity W x b b')
  intro ξ hξ
  simp only [Set.mem_ofPred_eq] at hξ ⊢
  push Not at hξ
  obtain ⟨ha, ha', hne⟩ := hξ
  refine ⟨fun h => hne h.symm, ?_⟩
  rw [sub_dotProduct, sub_eq_zero]
  exact act_val ha ha'

lemma resid_bound (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    ∑ i, |(b - A *ᵥ x) i| ≤ ((m : ℝ) * (1 + ∑ k, |x k|)) * (‖A‖ + ‖b‖) := by
  have hX : 0 ≤ ∑ k, |x k| := by positivity
  have hi : ∀ i, |(b - A *ᵥ x) i| ≤ (1 + ∑ k, |x k|) * (‖A‖ + ‖b‖) := by
    intro i
    have h1 : |(A *ᵥ x) i| ≤ ‖A i‖ * ∑ k, |x k| := abs_dot_le (A i) x
    have h2 : ‖A i‖ ≤ ‖A‖ := norm_le_pi_norm A i
    have h3 : |b i| ≤ ‖b‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm b i
    have h4 : |(b - A *ᵥ x) i| ≤ |b i| + |(A *ᵥ x) i| := by
      rw [Pi.sub_apply]; exact abs_sub _ _
    have h5 : ‖A i‖ * ∑ k, |x k| ≤ ‖A‖ * ∑ k, |x k| := mul_le_mul_of_nonneg_right h2 hX
    have hA0 : 0 ≤ ‖A‖ := norm_nonneg _
    have hb0 : 0 ≤ ‖b‖ := norm_nonneg _
    nlinarith
  calc ∑ i, |(b - A *ᵥ x) i| ≤ ∑ _i : Fin m, (1 + ∑ k, |x k|) * (‖A‖ + ‖b‖) :=
        Finset.sum_le_sum fun i _ => hi i
    _ = ((m : ℝ) * (1 + ∑ k, |x k|)) * (‖A‖ + ‖b‖) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

lemma rf_sub (T : Fin m → Fin n → ℝ) (h : Fin m → ℝ) (y x : Fin n → ℝ) :
    (h - T *ᵥ y) - (h - T *ᵥ x) = -(T *ᵥ (y - x)) := by
  rw [sub_sub_sub_cancel_left]
  ext i
  simp only [Pi.sub_apply, Pi.neg_apply, mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
  ring

lemma sum_abs_mulVec (T : Fin m → Fin n → ℝ) (v : Fin n → ℝ) :
    ∑ i, |(T *ᵥ v) i| ≤ (m : ℝ) * ‖T‖ * ((n : ℝ) * ‖v‖) := by
  have hv := sum_abs_le_norm v
  have hT0 : 0 ≤ ‖T‖ := norm_nonneg _
  calc ∑ i, |(T *ᵥ v) i| ≤ ∑ _i : Fin m, ‖T‖ * ((n : ℝ) * ‖v‖) := by
        refine Finset.sum_le_sum fun i _ => ?_
        calc |(T *ᵥ v) i| = |T i ⬝ᵥ v| := rfl
          _ ≤ ‖T i‖ * ∑ k, |v k| := abs_dot_le _ _
          _ ≤ ‖T‖ * ((n : ℝ) * ‖v‖) :=
            mul_le_mul (norm_le_pi_norm T i) hv (Finset.sum_nonneg fun _ _ => abs_nonneg _) hT0
    _ = (m : ℝ) * ‖T‖ * ((n : ℝ) * ‖v‖) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

lemma diff_bound (T : Fin m → Fin n → ℝ) (h : Fin m → ℝ) (y x : Fin n → ℝ) :
    ∑ i, |((h - T *ᵥ y) - (h - T *ᵥ x)) i| ≤ (m : ℝ) * ‖T‖ * ((n : ℝ) * ‖y - x‖) := by
  rw [rf_sub]
  have : ∀ i, |(-(T *ᵥ (y - x))) i| = |(T *ᵥ (y - x)) i| := fun i => by simp
  simp only [this]
  exact sum_abs_mulVec T (y - x)

/-- the integrand `psi` is integrable -/
lemma integrable_psi {μ : Measure (RecourseData m n p)} [IsProbabilityMeasure μ]
    (hmom : recourseMomentAlternative μ) {W : Matrix (Fin m) (Fin p) ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ b q, ‖piB W b q‖ ≤ C * ‖q‖) (x : Fin n → ℝ) :
    Integrable (fun ξ : RecourseData m n p => psi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x)) μ := by
  refine Integrable.mono' ((integrable_base hmom).const_mul (C * ((m : ℝ) * (1 + ∑ k, |x k|))))
    (measurable_psi W x).aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
  rw [Real.norm_eq_abs]
  refine (psi_bound hC0 hC _ _).trans ?_
  have h1 := resid_bound ξ.1 ξ.2.1 x
  have hq : 0 ≤ ‖ξ.2.2‖ := norm_nonneg _
  have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hC0 hq)
  calc C * ‖ξ.2.2‖ * ∑ i, |(ξ.2.1 - ξ.1 *ᵥ x) i|
      ≤ C * ‖ξ.2.2‖ * (((m : ℝ) * (1 + ∑ k, |x k|)) * (‖ξ.1‖ + ‖ξ.2.1‖)) := this
    _ = C * ((m : ℝ) * (1 + ∑ k, |x k|)) * ((‖ξ.1‖ + ‖ξ.2.1‖) * ‖ξ.2.2‖) := by ring

/-- the gradient field (as a vector): `-(Pi ᵥ* T)` -/
noncomputable def wf (W : Matrix (Fin m) (Fin p) ℝ) (x : Fin n → ℝ) (ξ : RecourseData m n p) :
    Fin n → ℝ :=
  -(Pi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) ᵥ* ξ.1)

lemma wf_dot (W : Matrix (Fin m) (Fin p) ℝ) (x y : Fin n → ℝ) (ξ : RecourseData m n p) :
    wf W x ξ ⬝ᵥ (y - x) =
      Pi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) ⬝ᵥ ((ξ.2.1 - ξ.1 *ᵥ y) - (ξ.2.1 - ξ.1 *ᵥ x)) := by
  unfold wf
  rw [rf_sub, dotProduct_neg, neg_dotProduct]
  congr 1
  exact (dotProduct_mulVec _ _ _).symm

lemma measurable_wf (W : Matrix (Fin m) (Fin p) ℝ) (x : Fin n → ℝ) (j : Fin n) :
    Measurable fun ξ : RecourseData m n p => wf W x ξ j := by
  unfold wf vecMul dotProduct
  simp only [Pi.neg_apply]
  refine (Finset.measurable_sum _ fun i _ => ?_).neg
  exact ((measurable_pi_iff.1 (measurable_Pi W x)) i).mul
    ((show Continuous fun ξ : RecourseData m n p => ξ.1 i j from
      (continuous_apply j).comp ((continuous_apply i).comp continuous_fst)).measurable)

lemma wf_bound {W : Matrix (Fin m) (Fin p) ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ b q, ‖piB W b q‖ ≤ C * ‖q‖) (x : Fin n → ℝ) (ξ : RecourseData m n p) (j : Fin n) :
    |wf W x ξ j| ≤ (C * m) * ((‖ξ.1‖ + ‖ξ.2.1‖) * ‖ξ.2.2‖) := by
  unfold wf
  rw [Pi.neg_apply, abs_neg]
  have hP := Pi_bound hC0 hC ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x)
  have h1 : (Pi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) ᵥ* ξ.1) j =
      Pi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) ⬝ᵥ (fun i => ξ.1 i j) := rfl
  rw [h1]
  refine (abs_dot_le _ _).trans ?_
  have h2 : ∑ i, |ξ.1 i j| ≤ (m : ℝ) * ‖ξ.1‖ := by
    calc ∑ i, |ξ.1 i j| ≤ ∑ _i : Fin m, ‖ξ.1‖ := Finset.sum_le_sum fun i _ => by
          have a := norm_le_pi_norm (ξ.1 i) j
          have b := norm_le_pi_norm ξ.1 i
          rw [Real.norm_eq_abs] at a
          exact a.trans b
      _ = (m : ℝ) * ‖ξ.1‖ := by simp
  have hq : 0 ≤ ‖ξ.2.2‖ := norm_nonneg _
  have hT : 0 ≤ ‖ξ.1‖ := norm_nonneg _
  have hh : 0 ≤ ‖ξ.2.1‖ := norm_nonneg _
  calc ‖Pi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x)‖ * ∑ i, |ξ.1 i j|
      ≤ (C * ‖ξ.2.2‖) * ((m : ℝ) * ‖ξ.1‖) :=
        mul_le_mul hP h2 (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)
    _ = (C * m) * (‖ξ.1‖ * ‖ξ.2.2‖) := by ring
    _ ≤ (C * m) * ((‖ξ.1‖ + ‖ξ.2.1‖) * ‖ξ.2.2‖) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith

/-- a vector as a continuous linear functional -/
noncomputable def cl (w : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ j, w j • ContinuousLinearMap.proj j

lemma cl_apply (w v : Fin n → ℝ) : cl w v = w ⬝ᵥ v := by
  simp [cl, dotProduct]

lemma continuous_cl : Continuous (cl : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ) :=
  continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const

/-- the gradient vector -/
noncomputable def Gv (μ : Measure (RecourseData m n p)) (W : Matrix (Fin m) (Fin p) ℝ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j => ∫ ξ, wf W x ξ j ∂μ

lemma continuous_rfy (ξ : RecourseData m n p) :
    Continuous fun y : Fin n → ℝ => ξ.2.1 - ξ.1 *ᵥ y :=
  continuous_const.sub (continuous_const.matrix_mulVec continuous_id)

/-- pointwise eventual constancy of `Pi` and linearity of `psi` -/
lemma eventually_pt {W : Matrix (Fin m) (Fin p) ℝ} (ξ : RecourseData m n p) (x : Fin n → ℝ)
    (hg : Good W ξ.2.2)
    (hu : ∀ b b', act W b ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) → act W b' ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) →
      piB W b' ξ.2.2 = piB W b ξ.2.2) :
    ∀ᶠ y in 𝓝 x, Pi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ y) = Pi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) ∧
      psi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ y) = Pi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) ⬝ᵥ (ξ.2.1 - ξ.1 *ᵥ y) := by
  have hev := eventually_linear hg (ξ.2.1 - ξ.1 *ᵥ x) hu
  exact ((continuous_rfy ξ).tendsto x).eventually hev

lemma Gv_continuousOn {μ : Measure (RecourseData m n p)} [IsProbabilityMeasure μ]
    {W : Matrix (Fin m) (Fin p) ℝ} (hrow : ∀ d, d ᵥ* W = 0 → d = 0)
    (hmom : recourseMomentAlternative μ)
    (hbelow : ∀ x ∈ recourseDomain μ W, ⊥ < extendedExpectedRecourse μ W x)
    (hdensity : μ ≪ volume) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ b q, ‖piB W b q‖ ≤ C * ‖q‖) :
    ContinuousOn (Gv μ W) (recourseDomain μ W) := by
  refine continuousOn_pi.2 fun j => ?_
  intro x hx
  have hae := (ae_good_eq hrow hx (hbelow x hx)).and (ae_uniq hdensity W x)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun ξ => (C * m) * ((‖ξ.1‖ + ‖ξ.2.1‖) * ‖ξ.2.2‖)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun y => (measurable_wf W y j).aestronglyMeasurable
  · exact Eventually.of_forall fun y => ae_of_all _ fun ξ => by
      rw [Real.norm_eq_abs]; exact wf_bound hC0 hC y ξ j
  · exact (integrable_base hmom).const_mul _
  · refine hae.mono fun ξ ⟨⟨hg, _⟩, hu⟩ => ?_
    have hev := eventually_pt ξ x hg hu
    refine tendsto_const_nhds.congr' ?_
    refine eventually_nhdsWithin_of_eventually_nhds (hev.mono fun y hy => ?_)
    simp only [wf, hy.1]

lemma Q_eq {μ : Measure (RecourseData m n p)} [IsProbabilityMeasure μ]
    {W : Matrix (Fin m) (Fin p) ℝ} (hrow : ∀ d, d ᵥ* W = 0 → d = 0) {x : Fin n → ℝ}
    (hx : x ∈ recourseDomain μ W) (hb : ⊥ < extendedExpectedRecourse μ W x) :
    KallMayer.Recourse.ExpectedRecourse μ W (fun d => d.1) (fun d => d.2.1) (fun d => d.2.2) x =
      ∫ ξ, psi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) ∂μ := by
  unfold KallMayer.Recourse.ExpectedRecourse
  refine integral_congr_ae ((ae_good_eq hrow hx hb).mono fun ξ h => ?_)
  change (KallMayer.Recourse.LPValue W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x)).toReal = _
  rw [h.2, EReal.toReal_coe]

lemma integrable_dot {μ : Measure (RecourseData m n p)} [IsProbabilityMeasure μ]
    (hmom : recourseMomentAlternative μ) {W : Matrix (Fin m) (Fin p) ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ b q, ‖piB W b q‖ ≤ C * ‖q‖) (x y : Fin n → ℝ) :
    Integrable (fun ξ : RecourseData m n p =>
      Pi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) ⬝ᵥ ((ξ.2.1 - ξ.1 *ᵥ y) - (ξ.2.1 - ξ.1 *ᵥ x))) μ := by
  refine Integrable.mono' ((integrable_base hmom).const_mul (C * ((m : ℝ) * ((n : ℝ) * ‖y - x‖))))
    ?_ (ae_of_all _ fun ξ => ?_)
  · unfold dotProduct
    refine (Finset.measurable_sum _ fun i _ => ?_).aestronglyMeasurable
    exact ((measurable_pi_iff.1 (measurable_Pi W x)) i).mul
      (((continuous_apply i).comp ((continuous_rf y).sub (continuous_rf x))).measurable)
  · rw [Real.norm_eq_abs]
    refine (abs_dot_le _ _).trans ?_
    have hP := Pi_bound hC0 hC ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x)
    have hD := diff_bound ξ.1 ξ.2.1 y x
    have hq : 0 ≤ ‖ξ.2.2‖ := norm_nonneg _
    have hT : 0 ≤ ‖ξ.1‖ := norm_nonneg _
    have hh : 0 ≤ ‖ξ.2.1‖ := norm_nonneg _
    have hyx : 0 ≤ ‖y - x‖ := norm_nonneg _
    calc ‖Pi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x)‖ * ∑ i, |((ξ.2.1 - ξ.1 *ᵥ y) - (ξ.2.1 - ξ.1 *ᵥ x)) i|
        ≤ (C * ‖ξ.2.2‖) * ((m : ℝ) * ‖ξ.1‖ * ((n : ℝ) * ‖y - x‖)) :=
          mul_le_mul hP hD (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)
      _ = C * ((m : ℝ) * ((n : ℝ) * ‖y - x‖)) * (‖ξ.1‖ * ‖ξ.2.2‖) := by ring
      _ ≤ C * ((m : ℝ) * ((n : ℝ) * ‖y - x‖)) * ((‖ξ.1‖ + ‖ξ.2.1‖) * ‖ξ.2.2‖) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith

lemma inv_norm_mul_le_one (v : Fin n → ℝ) : ‖v‖⁻¹ * ‖v‖ ≤ 1 := by
  by_cases h : ‖v‖ = 0
  · rw [h]; simp
  · rw [inv_mul_cancel₀ h]

/-- the key derivative estimate -/
lemma hasFDeriv {μ : Measure (RecourseData m n p)} [IsProbabilityMeasure μ]
    {W : Matrix (Fin m) (Fin p) ℝ} (hrow : ∀ d, d ᵥ* W = 0 → d = 0)
    (hmom : recourseMomentAlternative μ)
    (hbelow : ∀ x ∈ recourseDomain μ W, ⊥ < extendedExpectedRecourse μ W x)
    (hdensity : μ ≪ volume) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ b q, ‖piB W b q‖ ≤ C * ‖q‖) (x : Fin n → ℝ) (hx : x ∈ recourseDomain μ W) :
    HasFDerivWithinAt
      (KallMayer.Recourse.ExpectedRecourse μ W (fun d => d.1) (fun d => d.2.1) (fun d => d.2.2))
      (cl (Gv μ W x)) (recourseDomain μ W) x := by
  rw [hasFDerivWithinAt_iff_tendsto]
  set F : (Fin n → ℝ) → RecourseData m n p → ℝ := fun y ξ =>
    ‖y - x‖⁻¹ * (psi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ y) - psi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) -
      Pi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) ⬝ᵥ ((ξ.2.1 - ξ.1 *ᵥ y) - (ξ.2.1 - ξ.1 *ᵥ x))) with hF
  have hae := (ae_good_eq hrow hx (hbelow x hx)).and (ae_uniq hdensity W x)
  have hint : Tendsto (fun y => ∫ ξ, F y ξ ∂μ) (𝓝[recourseDomain μ W] x) (𝓝 (∫ _ξ, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun ξ => (2 * C * m * n) * ((‖ξ.1‖ + ‖ξ.2.1‖) * ‖ξ.2.2‖)) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun y => ?_
      refine Measurable.aestronglyMeasurable ?_
      refine measurable_const.mul (((measurable_psi W y).sub (measurable_psi W x)).sub ?_)
      unfold dotProduct
      refine Finset.measurable_sum _ fun i _ => ?_
      exact ((measurable_pi_iff.1 (measurable_Pi W x)) i).mul
        (((continuous_apply i).comp ((continuous_rf y).sub (continuous_rf x))).measurable)
    · refine Eventually.of_forall fun y => ae_of_all _ fun ξ => ?_
      simp only [hF, Real.norm_eq_abs, abs_mul, abs_inv, abs_norm]
      have hP := Pi_bound hC0 hC ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x)
      have hD := diff_bound ξ.1 ξ.2.1 y x
      have hL := psi_lip hC0 hC ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ y) (ξ.2.1 - ξ.1 *ᵥ x)
      have hdot := abs_dot_le (Pi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x)) ((ξ.2.1 - ξ.1 *ᵥ y) - (ξ.2.1 - ξ.1 *ᵥ x))
      have hq : 0 ≤ ‖ξ.2.2‖ := norm_nonneg _
      have hT : 0 ≤ ‖ξ.1‖ := norm_nonneg _
      have hh : 0 ≤ ‖ξ.2.1‖ := norm_nonneg _
      have hyx : 0 ≤ ‖y - x‖ := norm_nonneg _
      have hS : 0 ≤ ∑ i, |((ξ.2.1 - ξ.1 *ᵥ y) - (ξ.2.1 - ξ.1 *ᵥ x)) i| :=
        Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hinv : 0 ≤ ‖y - x‖⁻¹ := inv_nonneg.2 hyx
      have h1 : |psi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ y) - psi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) -
          Pi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) ⬝ᵥ ((ξ.2.1 - ξ.1 *ᵥ y) - (ξ.2.1 - ξ.1 *ᵥ x))| ≤
          (2 * C * ‖ξ.2.2‖) * ∑ i, |((ξ.2.1 - ξ.1 *ᵥ y) - (ξ.2.1 - ξ.1 *ᵥ x)) i| := by
        have := abs_sub _ _ |>.trans (add_le_add hL hdot)
        have h2 : ‖Pi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x)‖ *
            ∑ i, |((ξ.2.1 - ξ.1 *ᵥ y) - (ξ.2.1 - ξ.1 *ᵥ x)) i| ≤
            C * ‖ξ.2.2‖ * ∑ i, |((ξ.2.1 - ξ.1 *ᵥ y) - (ξ.2.1 - ξ.1 *ᵥ x)) i| :=
          mul_le_mul_of_nonneg_right hP hS
        linarith
      have h3 : (2 * C * ‖ξ.2.2‖) * ∑ i, |((ξ.2.1 - ξ.1 *ᵥ y) - (ξ.2.1 - ξ.1 *ᵥ x)) i| ≤
          (2 * C * ‖ξ.2.2‖) * ((m : ℝ) * ‖ξ.1‖ * ((n : ℝ) * ‖y - x‖)) :=
        mul_le_mul_of_nonneg_left hD (by positivity)
      have h4 := inv_norm_mul_le_one (y - x)
      calc ‖y - x‖⁻¹ * |psi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ y) - psi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) -
            Pi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) ⬝ᵥ ((ξ.2.1 - ξ.1 *ᵥ y) - (ξ.2.1 - ξ.1 *ᵥ x))|
          ≤ ‖y - x‖⁻¹ * ((2 * C * ‖ξ.2.2‖) * ((m : ℝ) * ‖ξ.1‖ * ((n : ℝ) * ‖y - x‖))) :=
            mul_le_mul_of_nonneg_left (h1.trans h3) hinv
        _ = (‖y - x‖⁻¹ * ‖y - x‖) * ((2 * C * m * n) * (‖ξ.1‖ * ‖ξ.2.2‖)) := by ring
        _ ≤ 1 * ((2 * C * m * n) * (‖ξ.1‖ * ‖ξ.2.2‖)) :=
            mul_le_mul_of_nonneg_right h4 (by positivity)
        _ = (2 * C * m * n) * (‖ξ.1‖ * ‖ξ.2.2‖) := one_mul _
        _ ≤ (2 * C * m * n) * ((‖ξ.1‖ + ‖ξ.2.1‖) * ‖ξ.2.2‖) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            nlinarith
    · exact (integrable_base hmom).const_mul _
    · refine hae.mono fun ξ ⟨⟨hg, _⟩, hu⟩ => ?_
      have hev := eventually_pt ξ x hg hu
      refine tendsto_const_nhds.congr' ?_
      refine eventually_nhdsWithin_of_eventually_nhds (hev.mono fun y hy => ?_)
      simp only [hF]
      rw [hy.2]
      unfold psi
      rw [dotProduct_sub (Pi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x)) (ξ.2.1 - ξ.1 *ᵥ y) (ξ.2.1 - ξ.1 *ᵥ x)]
      ring
  rw [integral_zero] at hint
  have hint' := hint.norm
  rw [norm_zero] at hint'
  refine hint'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  -- identity for y ∈ K
  have hQy := Q_eq hrow hy (hbelow y hy)
  have hQx := Q_eq hrow hx (hbelow x hx)
  have hg : cl (Gv μ W x) (y - x) = ∫ ξ, Pi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) ⬝ᵥ
      ((ξ.2.1 - ξ.1 *ᵥ y) - (ξ.2.1 - ξ.1 *ᵥ x)) ∂μ := by
    rw [cl_apply]
    have : ∀ ξ : RecourseData m n p, Pi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) ⬝ᵥ
        ((ξ.2.1 - ξ.1 *ᵥ y) - (ξ.2.1 - ξ.1 *ᵥ x)) = ∑ j, wf W x ξ j * (y - x) j := by
      intro ξ; rw [← wf_dot]; rfl
    simp only [this]
    rw [integral_finsetSum]
    · unfold Gv dotProduct
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_mul_const]
    · intro j _
      refine ((Integrable.mono' ((integrable_base hmom).const_mul (C * m))
        (measurable_wf W x j).aestronglyMeasurable (ae_of_all _ fun ξ => ?_))).mul_const _
      rw [Real.norm_eq_abs]; exact wf_bound hC0 hC x ξ j
  have hE : KallMayer.Recourse.ExpectedRecourse μ W (fun d => d.1) (fun d => d.2.1) (fun d => d.2.2) y -
      KallMayer.Recourse.ExpectedRecourse μ W (fun d => d.1) (fun d => d.2.1) (fun d => d.2.2) x -
      cl (Gv μ W x) (y - x) =
      ∫ ξ, (psi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ y) - psi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) -
        Pi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) ⬝ᵥ ((ξ.2.1 - ξ.1 *ᵥ y) - (ξ.2.1 - ξ.1 *ᵥ x))) ∂μ := by
    rw [hQy, hQx, hg, ← integral_sub, ← integral_sub]
    · exact (integrable_psi hmom hC0 hC y).sub (integrable_psi hmom hC0 hC x)
    · exact integrable_dot hmom hC0 hC x y
    · exact integrable_psi hmom hC0 hC y
    · exact integrable_psi hmom hC0 hC x
  show ‖∫ ξ, F y ξ ∂μ‖ = ‖y - x‖⁻¹ * ‖_‖
  rw [hE]
  simp only [hF]
  rw [integral_const_mul, norm_mul, Real.norm_eq_abs, abs_inv, abs_norm]

/-- the degenerate case: no full row rank forces an empty domain -/
lemma domain_empty {μ : Measure (RecourseData m n p)} [IsProbabilityMeasure μ]
    {W : Matrix (Fin m) (Fin p) ℝ} (hdensity : μ ≪ volume)
    (hrow : ¬ ∀ d, d ᵥ* W = 0 → d = 0) (x : Fin n → ℝ) : x ∉ recourseDomain μ W := by
  intro hx
  push Not at hrow
  obtain ⟨d, hdW, hd⟩ := hrow
  have hfe := ae_feas hx
  have h1 : ∀ᵐ ξ ∂μ, d ⬝ᵥ (ξ.2.1 - ξ.1 *ᵥ x) = 0 := by
    refine hfe.mono fun ξ ⟨z, hz⟩ => ?_
    rw [← hz.2, dotProduct_mulVec, hdW, zero_dotProduct]
  rw [ae_iff] at h1
  have h2 := hrow_null hdensity x d hd
  have h3 := measure_univ_le_add_compl (μ := μ) {ξ : RecourseData m n p | d ⬝ᵥ (ξ.2.1 - ξ.1 *ᵥ x) = 0}
  rw [h2, measure_univ] at h3
  have : μ ({ξ : RecourseData m n p | d ⬝ᵥ (ξ.2.1 - ξ.1 *ᵥ x) = 0}ᶜ) = 0 := h1
  rw [this] at h3
  simp at h3

theorem expected_recourse_contDiffOn_core {m n p : ℕ}
    (μ : Measure (RecourseData m n p)) [IsProbabilityMeasure μ]
    (W : Matrix (Fin m) (Fin p) ℝ)
    (hmom : recourseMomentAlternative μ)
    (hbelow : ∀ x ∈ recourseDomain μ W, ⊥ < extendedExpectedRecourse μ W x)
    (hdensity : μ ≪ volume) :
    (∀ x ∈ recourseDomain μ W,
      (∀ᵐ d ∂μ, ∃ v : ℝ,
        KallMayer.Recourse.PointwiseRecourse W d.1 d.2.1 d.2.2 x = (v : EReal)) ∧
      Integrable (fun d =>
        (KallMayer.Recourse.PointwiseRecourse W d.1 d.2.1 d.2.2 x).toReal) μ) ∧
    ∃ g : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] ℝ),
      ContinuousOn g (recourseDomain μ W) ∧
      ∀ x ∈ recourseDomain μ W,
        HasFDerivWithinAt
          (KallMayer.Recourse.ExpectedRecourse μ W
            (fun d => d.1) (fun d => d.2.1) (fun d => d.2.2))
          (g x) (recourseDomain μ W) x := by
  by_cases hrow : ∀ d, d ᵥ* W = 0 → d = 0
  · obtain ⟨C, hC0, hC⟩ := piB_bound W
    refine ⟨fun x hx => ⟨?_, ?_⟩, fun x => cl (Gv μ W x), ?_, fun x hx => ?_⟩
    · exact (ae_good_eq hrow hx (hbelow x hx)).mono fun ξ h => ⟨_, h.2⟩
    · refine (integrable_psi hmom hC0 hC x).congr
        ((ae_good_eq hrow hx (hbelow x hx)).mono fun ξ h => ?_)
      change psi W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x) =
        (KallMayer.Recourse.LPValue W ξ.2.2 (ξ.2.1 - ξ.1 *ᵥ x)).toReal
      rw [h.2, EReal.toReal_coe]
    · exact continuous_cl.comp_continuousOn (Gv_continuousOn hrow hmom hbelow hdensity hC0 hC)
    · exact hasFDeriv hrow hmom hbelow hdensity hC0 hC x hx
  · refine ⟨fun x hx => absurd hx (domain_empty hdensity hrow x), fun _ => 0,
      continuousOn_const, fun x hx => absurd hx (domain_empty hdensity hrow x)⟩

end Part3

end Kall1976

open Kall1976


theorem solution {m n p : ℕ}
    (μ : Measure (RecourseData m n p)) [IsProbabilityMeasure μ]
    (W : Matrix (Fin m) (Fin p) ℝ)
    (hmom : recourseMomentAlternative μ)
    (hbelow : ∀ x ∈ recourseDomain μ W, ⊥ < extendedExpectedRecourse μ W x)
    (hdensity : μ ≪ volume) :
    (∀ x ∈ recourseDomain μ W,
      (∀ᵐ d ∂μ, ∃ v : ℝ,
        KallMayer.Recourse.PointwiseRecourse W d.1 d.2.1 d.2.2 x = (v : EReal)) ∧
      Integrable (fun d =>
        (KallMayer.Recourse.PointwiseRecourse W d.1 d.2.1 d.2.2 x).toReal) μ) ∧
    ∃ g : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] ℝ),
      ContinuousOn g (recourseDomain μ W) ∧
      ∀ x ∈ recourseDomain μ W,
        HasFDerivWithinAt
          (KallMayer.Recourse.ExpectedRecourse μ W
            (fun d => d.1) (fun d => d.2.1) (fun d => d.2.2))
          (g x) (recourseDomain μ W) x := by
  exact expected_recourse_contDiffOn_core μ W hmom hbelow hdensity
