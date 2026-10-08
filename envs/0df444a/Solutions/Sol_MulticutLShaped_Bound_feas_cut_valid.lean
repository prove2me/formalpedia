-- Prove2me | solution 1 for MulticutLShaped.Bound.feas_cut_valid
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T04:17:11.517984+00:00
-- url     : https://prove2.me/submissions/74080c16-58de-4730-b8c8-fc7ccc567267

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_LShaped_Bases
import Definitions.Def_MulticutLShaped_Bound_Cuts
import Definitions.Def_MulticutLShaped_Bound_Masters
import Definitions.Def_MulticutLShaped_Bound_Algorithm

open StochasticProg.Recourse StochasticProg.LShaped
open scoped Matrix

namespace MulticutLShaped.Bound

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

variable {n1 n2 m1 m2 K : ℕ}

lemma t1_foldr_top (l : List EReal) : l.foldr bookAdd 0 = ⊤ ↔ ⊤ ∈ l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons, List.mem_cons]
    unfold bookAdd
    split_ifs with h
    · rcases h with h | h
      · simp [h]
      · simp [ih.mp h]
    · push_neg at h
      constructor
      · intro h'; exact absurd h' (EReal.add_ne_top h.1 h.2)
      · rintro (h' | h')
        · exact absurd h'.symm h.1
        · exact absurd (ih.mpr h') h.2

lemma t1_QVal_top (inst : Instance n1 n2 m1 m2 K) (x : Fin n1 → ℝ) (k : Fin K) :
    QVal inst x k = ⊤ ↔ ¬ ∃ y : Fin n2 → ℝ, (∀ i, 0 ≤ y i) ∧
      Matrix.mulVec inst.W y = inst.h k - Matrix.mulVec (inst.T k) x := by
  unfold QVal
  rw [sInf_eq_top]
  constructor
  · rintro h ⟨y, hy, hW⟩
    exact EReal.coe_ne_top _ (h _ ⟨y, hy, hW, rfl⟩)
  · rintro h z ⟨y, hy, hW, rfl⟩
    exact absurd ⟨y, hy, hW⟩ h

lemma t1_mem_K2 (inst : Instance n1 n2 m1 m2 K) (hp_pos : ∀ k, 0 < inst.p k) (x : Fin n1 → ℝ) :
    x ∈ K2 inst ↔ ∀ k, ∃ y : Fin n2 → ℝ, (∀ i, 0 ≤ y i) ∧
      Matrix.mulVec inst.W y = inst.h k - Matrix.mulVec (inst.T k) x := by
  unfold K2 Q
  simp only [Set.mem_setOf_eq, ne_eq, t1_foldr_top, List.mem_ofFn, Set.mem_range, not_exists]
  apply forall_congr'
  intro k
  rw [← not_iff_not, not_not, ← t1_QVal_top]
  constructor
  · intro h
    rw [EReal.mul_eq_top] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩ | ⟨_, h2⟩
    · exact absurd h1 (EReal.coe_ne_bot _)
    · exact absurd h1 (not_lt.mpr (EReal.coe_nonneg.mpr (inst.hp_nonneg k)))
    · exact absurd h1 (EReal.coe_ne_top _)
    · exact h2
  · intro h
    rw [h]
    exact EReal.mul_top_of_pos (EReal.coe_pos.mpr (hp_pos k))
open Matrix

noncomputable def rr (inst : Instance n1 n2 m1 m2 K) (k : Fin K) (x : Fin n1 → ℝ) : Fin m2 → ℝ :=
  inst.h k - inst.T k *ᵥ x

def SFeas (inst : Instance n1 n2 m1 m2 K) (k : Fin K) (x : Fin n1 → ℝ) : Prop :=
  ∃ y : Fin n2 → ℝ, (∀ i, 0 ≤ y i) ∧ inst.W *ᵥ y = rr inst k x

lemma basisValue_eq (inst : Instance n1 n2 m1 m2 K) (k : Fin K) (b : Basis n2 m2)
    (x : Fin n1 → ℝ) :
    basisValue inst k b x = multiplier inst b (inst.q k) ⬝ᵥ rr inst k x := by
  simp [basisValue, rr, dotProduct_sub]

lemma feasBasisValue_eq (inst : Instance n1 n2 m1 m2 K) (k : Fin K) (b : FeasBasis n2 m2)
    (x : Fin n1 → ℝ) :
    feasBasisValue inst k b x = feasMultiplier inst b ⬝ᵥ rr inst k x := by
  simp [feasBasisValue, rr, dotProduct_sub]

lemma feasCut_iff (inst : Instance n1 n2 m1 m2 K) (k : Fin K) (b : FeasBasis n2 m2)
    (x : Fin n1 → ℝ) :
    (feasCutCoeffs inst k b).2 ≤ (feasCutCoeffs inst k b).1 ⬝ᵥ x ↔
      feasBasisValue inst k b x ≤ 0 := by
  have : (feasCutCoeffs inst k b).1 ⬝ᵥ x = feasMultiplier inst b ⬝ᵥ (inst.T k *ᵥ x) := by
    rw [dotProduct_mulVec]; rfl
  have h2 : (feasCutCoeffs inst k b).2 = feasMultiplier inst b ⬝ᵥ inst.h k := rfl
  simp only [feasBasisValue]
  rw [this, h2]
  constructor <;> intro h <;> linarith

lemma optCut_eq (inst : Instance n1 n2 m1 m2 K) (β : Fin K → Basis n2 m2) (x : Fin n1 → ℝ) :
    (optCutCoeffs inst β).2 - (optCutCoeffs inst β).1 ⬝ᵥ x =
      ∑ k, inst.p k * basisValue inst k (β k) x := by
  have h1 : (optCutCoeffs inst β).1 =
      ∑ k, inst.p k • (multiplier inst (β k) (inst.q k) ᵥ* inst.T k) := by
    funext i
    simp [optCutCoeffs, Finset.sum_apply, vecMul]
  have h2 : (optCutCoeffs inst β).1 ⬝ᵥ x =
      ∑ k, inst.p k * (multiplier inst (β k) (inst.q k) ⬝ᵥ (inst.T k *ᵥ x)) := by
    rw [h1]
    simp only [dotProduct_mulVec]
    simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  rw [h2]
  simp only [optCutCoeffs, basisValue, mul_sub, Finset.sum_sub_distrib]

lemma QVal_le (inst : Instance n1 n2 m1 m2 K) (k : Fin K) (x : Fin n1 → ℝ) (y : Fin n2 → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hW : inst.W *ᵥ y = rr inst k x) :
    QVal inst x k ≤ ((inst.q k ⬝ᵥ y : ℝ) : EReal) :=
  sInf_le ⟨y, hy, hW, rfl⟩

lemma QVal_ge_dual (inst : Instance n1 n2 m1 m2 K) (k : Fin K) (x : Fin n1 → ℝ)
    (π : Fin m2 → ℝ) (hπ : ∀ j, (π ᵥ* inst.W) j ≤ inst.q k j) :
    ((π ⬝ᵥ rr inst k x : ℝ) : EReal) ≤ QVal inst x k := by
  apply le_sInf
  rintro z ⟨y, hy, hW, rfl⟩
  exact EReal.coe_le_coe_iff.mpr (LPB.weak_dual inst.W (rr inst k x) (inst.q k) π hπ y ⟨hy, hW⟩)

lemma rec_opt (inst : Instance n1 n2 m1 m2 K) (hrow : ∀ d, d ᵥ* inst.W = 0 → d = 0)
    (k : Fin K) (x : Fin n1 → ℝ) (hfeas : SFeas inst k x) (hbot : QVal inst x k ≠ ⊥) :
    ∃ b : Basis n2 m2, (∀ j, (multiplier inst b (inst.q k) ᵥ* inst.W) j ≤ inst.q k j) ∧
      (basisValue inst k b x : EReal) = QVal inst x k := by
  obtain ⟨y0, hy0, hW0⟩ := hfeas
  have htop : QVal inst x k ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) (QVal_le inst k x y0 hy0 hW0)
  set v := (QVal inst x k).toReal
  have hv : (v : EReal) = QVal inst x k := EReal.coe_toReal htop hbot
  have hL : ∀ z, LPB.PFeas inst.W (rr inst k x) z → v ≤ inst.q k ⬝ᵥ z := by
    intro z hz
    have := QVal_le inst k x z hz.1 hz.2
    rw [← hv] at this
    exact EReal.coe_le_coe_iff.mp this
  obtain ⟨b, hb, hdual, zs, hzs, hmin, heq⟩ :=
    LPB.lpb inst.W hrow (rr inst k x) (inst.q k) v hL y0 ⟨hy0, hW0⟩
  let bb : Basis n2 m2 := ⟨b, hb⟩
  refine ⟨bb, hdual, ?_⟩
  rw [basisValue_eq inst k bb x]
  show (((((inst.W.submatrix id b)ᵀ)⁻¹ *ᵥ (fun i => inst.q k (b i))) ⬝ᵥ rr inst k x : ℝ) : EReal) =
    QVal inst x k
  rw [← heq]
  apply le_antisymm
  · apply le_sInf
    rintro z ⟨y, hy, hW, rfl⟩
    exact EReal.coe_le_coe_iff.mpr (hmin y ⟨hy, hW⟩)
  · exact QVal_le inst k x zs hzs.1 hzs.2

lemma feasMatrix_mulVec (inst : Instance n1 n2 m1 m2 K) (z : Fin n2 ⊕ Fin m2 ⊕ Fin m2 → ℝ) :
    feasMatrix inst *ᵥ z = inst.W *ᵥ (fun j => z (Sum.inl j)) +
      (fun i => z (Sum.inr (Sum.inl i))) - (fun i => z (Sum.inr (Sum.inr i))) := by
  funext i
  simp [mulVec, dotProduct, feasMatrix, Fintype.sum_sum_type]
  ring

lemma feasCost_dot (z : Fin n2 ⊕ Fin m2 ⊕ Fin m2 → ℝ) :
    (feasCost : Fin n2 ⊕ Fin m2 ⊕ Fin m2 → ℝ) ⬝ᵥ z =
      (∑ i, z (Sum.inr (Sum.inl i))) + ∑ i, z (Sum.inr (Sum.inr i)) := by
  simp [dotProduct, feasCost, Fintype.sum_sum_type]

lemma feasMul_W (inst : Instance n1 n2 m1 m2 K) (σ : Fin m2 → ℝ) (j : Fin n2) :
    (σ ᵥ* feasMatrix inst) (Sum.inl j) = (σ ᵥ* inst.W) j := by
  simp [vecMul, dotProduct, feasMatrix]

lemma feas_opt (inst : Instance n1 n2 m1 m2 K) (k : Fin K) (x : Fin n1 → ℝ) :
    ∃ b : FeasBasis n2 m2, (∀ j, (feasMultiplier inst b ᵥ* inst.W) j ≤ 0) ∧
      feasBasisValue inst k b x = feasLPValue inst k x ∧
      (¬ SFeas inst k x → 0 < feasLPValue inst k x) := by
  have hrow : ∀ d, d ᵥ* feasMatrix inst = 0 → d = 0 := by
    intro d h
    funext j
    have := congrFun h (Sum.inr (Sum.inl j))
    simpa [vecMul, dotProduct, feasMatrix] using this
  set r := rr inst k x
  have hcostnn : ∀ z : Fin n2 ⊕ Fin m2 ⊕ Fin m2 → ℝ, (∀ j, 0 ≤ z j) →
      0 ≤ (feasCost : Fin n2 ⊕ Fin m2 ⊕ Fin m2 → ℝ) ⬝ᵥ z := by
    intro z hz
    rw [feasCost_dot]
    exact add_nonneg (Finset.sum_nonneg (fun i _ => hz _)) (Finset.sum_nonneg (fun i _ => hz _))
  let z0 : Fin n2 ⊕ Fin m2 ⊕ Fin m2 → ℝ :=
    Sum.elim 0 (Sum.elim (fun i => max (r i) 0) (fun i => max (-(r i)) 0))
  have hz0 : LPB.PFeas (feasMatrix inst) r z0 := by
    refine ⟨fun j => ?_, ?_⟩
    · rcases j with j | j | j <;> simp [z0]
    · rw [feasMatrix_mulVec]
      funext i
      simp only [z0, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Pi.sub_apply]
      have : (inst.W *ᵥ fun j => (0 : Fin n2 → ℝ) j) i = 0 := by simp [mulVec, dotProduct]
      rw [this]
      rcases le_total 0 (r i) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; simp
      · rw [max_eq_right h, max_eq_left (by linarith)]; simp
  obtain ⟨b, hb, hdual, zs, hzs, hmin, heq⟩ :=
    LPB.lpb (feasMatrix inst) hrow r feasCost 0 (fun z hz => hcostnn z hz.1) z0 hz0
  have hval : feasLPValue inst k x = (feasCost : Fin n2 ⊕ Fin m2 ⊕ Fin m2 → ℝ) ⬝ᵥ zs := by
    apply IsLeast.csInf_eq
    constructor
    · refine ⟨fun j => zs (Sum.inl j), fun i => zs (Sum.inr (Sum.inl i)),
        fun i => zs (Sum.inr (Sum.inr i)), fun _ => hzs.1 _, fun _ => hzs.1 _, fun _ => hzs.1 _,
        ?_, by rw [feasCost_dot]⟩
      rw [← feasMatrix_mulVec]; exact hzs.2
    · rintro w ⟨y, vp, vn, hy, hvp, hvn, hW, rfl⟩
      let z : Fin n2 ⊕ Fin m2 ⊕ Fin m2 → ℝ := Sum.elim y (Sum.elim vp vn)
      have hz : LPB.PFeas (feasMatrix inst) r z := by
        refine ⟨fun j => ?_, ?_⟩
        · rcases j with j | j | j <;> simp [z, hy, hvp, hvn]
        · rw [feasMatrix_mulVec]; simpa [z, r, rr] using hW
      have := hmin z hz
      rw [feasCost_dot z] at this
      simpa [z] using this
  let bb : FeasBasis n2 m2 := ⟨b, hb⟩
  refine ⟨bb, fun j => ?_, ?_, ?_⟩
  · have := hdual (Sum.inl j)
    rw [feasMul_W] at this
    exact this
  · rw [feasBasisValue_eq inst k bb x, hval, heq]; rfl
  · intro hnf
    rw [hval]
    rcases (hcostnn zs hzs.1).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hnf
      rw [feasCost_dot] at h
      have h1 : ∀ i, zs (Sum.inr (Sum.inl i)) = 0 := by
        have := (add_eq_zero_iff_of_nonneg (Finset.sum_nonneg (fun i _ => hzs.1 (Sum.inr (Sum.inl i))))
          (Finset.sum_nonneg (fun i _ => hzs.1 (Sum.inr (Sum.inr i))))).mp h.symm
        intro i
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hzs.1 _)).mp this.1 i (Finset.mem_univ _)
      have h2 : ∀ i, zs (Sum.inr (Sum.inr i)) = 0 := by
        have := (add_eq_zero_iff_of_nonneg (Finset.sum_nonneg (fun i _ => hzs.1 (Sum.inr (Sum.inl i))))
          (Finset.sum_nonneg (fun i _ => hzs.1 (Sum.inr (Sum.inr i))))).mp h.symm
        intro i
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hzs.1 _)).mp this.2 i (Finset.mem_univ _)
      refine ⟨fun j => zs (Sum.inl j), fun _ => hzs.1 _, ?_⟩
      have := hzs.2
      rw [feasMatrix_mulVec] at this
      rw [show rr inst k x = r from rfl, ← this]
      funext i
      simp [h1, h2]

lemma feasCut_valid (inst : Instance n1 n2 m1 m2 K) (k : Fin K) (b : FeasBasis n2 m2)
    (hb : ∀ j, (feasMultiplier inst b ᵥ* inst.W) j ≤ 0) (x : Fin n1 → ℝ) (hx : SFeas inst k x) :
    feasBasisValue inst k b x ≤ 0 := by
  obtain ⟨y, hy, hW⟩ := hx
  rw [feasBasisValue_eq, ← hW, dotProduct_mulVec]
  exact Finset.sum_nonpos (fun j _ => mul_nonpos_of_nonpos_of_nonneg (hb j) (hy j))


lemma foldr_coe (l : List ℝ) :
    (l.map (fun a : ℝ => (a : EReal))).foldr bookAdd 0 = ((l.sum : ℝ) : EReal) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons, List.sum_cons, ih]
    unfold bookAdd
    rw [if_neg (by simp)]
    exact (EReal.coe_add _ _).symm

lemma Q_coe (inst : Instance n1 n2 m1 m2 K) (x : Fin n1 → ℝ) (v : Fin K → ℝ)
    (hv : ∀ k, QVal inst x k = (v k : EReal)) :
    Q inst x = ((∑ k, inst.p k * v k : ℝ) : EReal) := by
  unfold Q
  have : List.ofFn (fun k => (inst.p k : EReal) * QVal inst x k) =
      (List.ofFn (fun k => inst.p k * v k)).map (fun a : ℝ => (a : EReal)) := by
    rw [List.map_ofFn]
    congr 1
    funext k
    simp [hv k]
  rw [this, foldr_coe, List.sum_ofFn]



lemma ereal_pmul_le (p a : ℝ) (hp : 0 ≤ p) (Qv : EReal) (h : (a : EReal) ≤ Qv) :
    ((p * a : ℝ) : EReal) ≤ (p : EReal) * Qv := by
  by_cases htop : Qv = ⊤
  · rw [htop]
    rcases hp.lt_or_eq with hp | hp
    · rw [EReal.mul_top_of_pos (EReal.coe_pos.mpr hp)]; exact le_top
    · rw [← hp]; simp
  · have hbot : Qv ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot a) h
    rw [← EReal.coe_toReal htop hbot] at h ⊢
    rw [← EReal.coe_mul, EReal.coe_le_coe_iff]
    exact mul_le_mul_of_nonneg_left (EReal.coe_le_coe_iff.mp h) hp

lemma optCut_val (inst : Instance n1 n2 m1 m2 K) (k : Fin K) (b : Basis n2 m2) (x : Fin n1 → ℝ) :
    (optCut inst k b).2 - (optCut inst k b).1 ⬝ᵥ x =
      inst.p k * (multiplier inst b (inst.q k) ⬝ᵥ rr inst k x) := by
  simp only [optCut, smul_dotProduct, smul_eq_mul, rr, dotProduct_sub, dotProduct_mulVec]
  ring

lemma simplex_val (inst : Instance n1 n2 m1 m2 K) (k : Fin K) (b : Basis n2 m2) (x : Fin n1 → ℝ)
    (hb : IsSimplexOptimal inst k b x) :
    ((multiplier inst b (inst.q k) ⬝ᵥ rr inst k x : ℝ) : EReal) = QVal inst x k := by
  obtain ⟨hU, hprim, hdual⟩ := hb
  set Wb := inst.W.submatrix id b.1 with hWb
  set yB := Wb⁻¹ *ᵥ rr inst k x with hyB
  let y : Fin n2 → ℝ := fun j => ∑ i, if b.1 i = j then yB i else 0
  have hy : ∀ j, 0 ≤ y j := fun j => Finset.sum_nonneg (fun i _ => by
    split_ifs
    · exact hprim i
    · exact le_rfl)
  have hWy : inst.W *ᵥ y = Wb *ᵥ yB := by
    funext r
    simp only [y, mulVec, dotProduct, Finset.mul_sum, hWb, submatrix_apply, id]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq']
    simp
  have hWbyB : Wb *ᵥ yB = rr inst k x := by
    rw [hyB, mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]
  have hqy : inst.q k ⬝ᵥ y = (fun i => inst.q k (b.1 i)) ⬝ᵥ yB := by
    simp only [y, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq']
    simp
  have hπ : multiplier inst b (inst.q k) ⬝ᵥ rr inst k x = inst.q k ⬝ᵥ y := by
    rw [hqy, ← hWbyB, dotProduct_mulVec]
    congr 1
    have hU' : IsUnit (Wbᵀ).det := by rw [det_transpose]; exact hU
    rw [← mulVec_transpose]
    show Wbᵀ *ᵥ ((Wbᵀ)⁻¹ *ᵥ (fun i => inst.q k (b.1 i))) = _
    rw [mulVec_mulVec, mul_nonsing_inv _ hU', one_mulVec]
  apply le_antisymm
  · exact QVal_ge_dual inst k x _ hdual
  · rw [hπ]; exact QVal_le inst k x y hy (by rw [hWy, hWbyB])

theorem opt_cut_core (inst : Instance n1 n2 m1 m2 K) (k : Fin K)
    (b : Basis n2 m2) (x' : Fin n1 → ℝ) (hb : IsSimplexOptimal inst k b x') :
    (∀ x : Fin n1 → ℝ, (((optCut inst k b).2 - (optCut inst k b).1 ⬝ᵥ x : ℝ) : EReal) ≤
      (inst.p k : EReal) * QVal inst x k) ∧
    (((optCut inst k b).2 - (optCut inst k b).1 ⬝ᵥ x' : ℝ) : EReal) =
      (inst.p k : EReal) * QVal inst x' k := by
  refine ⟨fun x => ?_, ?_⟩
  · rw [optCut_val]
    exact ereal_pmul_le _ _ (inst.hp_nonneg k) _ (QVal_ge_dual inst k x _ hb.2.2)
  · rw [optCut_val, ← simplex_val inst k b x' hb, EReal.coe_mul]


lemma feas_opt2 (inst : Instance n1 n2 m1 m2 K) (k : Fin K) (x : Fin n1 → ℝ)
    (hnf : ¬ SFeas inst k x) :
    ∃ b : FeasBasis n2 m2, IsFeasSimplexOptimal inst k b x ∧ 0 < feasBasisValue inst k b x := by
  have hrow : ∀ d, d ᵥ* feasMatrix inst = 0 → d = 0 := by
    intro d h
    funext j
    have := congrFun h (Sum.inr (Sum.inl j))
    simpa [vecMul, dotProduct, feasMatrix] using this
  set r := rr inst k x
  have hcostnn : ∀ z : Fin n2 ⊕ Fin m2 ⊕ Fin m2 → ℝ, (∀ j, 0 ≤ z j) →
      0 ≤ (feasCost : Fin n2 ⊕ Fin m2 ⊕ Fin m2 → ℝ) ⬝ᵥ z := by
    intro z hz
    rw [feasCost_dot]
    exact add_nonneg (Finset.sum_nonneg (fun i _ => hz _)) (Finset.sum_nonneg (fun i _ => hz _))
  let z0 : Fin n2 ⊕ Fin m2 ⊕ Fin m2 → ℝ :=
    Sum.elim 0 (Sum.elim (fun i => max (r i) 0) (fun i => max (-(r i)) 0))
  have hz0 : LPB.PFeas (feasMatrix inst) r z0 := by
    refine ⟨fun j => ?_, ?_⟩
    · rcases j with j | j | j <;> simp [z0]
    · rw [feasMatrix_mulVec]
      funext i
      simp only [z0, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Pi.sub_apply]
      have : (inst.W *ᵥ fun j => (0 : Fin n2 → ℝ) j) i = 0 := by simp [mulVec, dotProduct]
      rw [this]
      rcases le_total 0 (r i) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; simp
      · rw [max_eq_right h, max_eq_left (by linarith)]; simp
  obtain ⟨b, hb, hU, hprim, hdual, zs, hzs, hmin, heq⟩ :=
    LPB.opt_basis (feasMatrix inst) hrow r feasCost 0 (fun z hz => hcostnn z hz.1) z0 hz0
  let bb : FeasBasis n2 m2 := ⟨b, hb⟩
  refine ⟨bb, ⟨hU, hprim, hdual⟩, ?_⟩
  rw [feasBasisValue_eq inst k bb x]
  show 0 < (((feasMatrix inst).submatrix id b)ᵀ)⁻¹ *ᵥ (fun i => feasCost (b i)) ⬝ᵥ r
  rw [← heq]
  rcases (hcostnn zs hzs.1).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hnf
    rw [feasCost_dot] at h
    have := (add_eq_zero_iff_of_nonneg (Finset.sum_nonneg (fun i _ => hzs.1 (Sum.inr (Sum.inl i))))
          (Finset.sum_nonneg (fun i _ => hzs.1 (Sum.inr (Sum.inr i))))).mp h.symm
    have h1 : ∀ i, zs (Sum.inr (Sum.inl i)) = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hzs.1 _)).mp this.1 i (Finset.mem_univ _)
    have h2 : ∀ i, zs (Sum.inr (Sum.inr i)) = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hzs.1 _)).mp this.2 i (Finset.mem_univ _)
    refine ⟨fun j => zs (Sum.inl j), fun _ => hzs.1 _, ?_⟩
    have := hzs.2
    rw [feasMatrix_mulVec] at this
    rw [show rr inst k x = r from rfl, ← this]
    funext i
    simp [h1, h2]

lemma feas_dual_W (inst : Instance n1 n2 m1 m2 K) (k : Fin K) (b : FeasBasis n2 m2)
    (x' : Fin n1 → ℝ) (hb : IsFeasSimplexOptimal inst k b x') :
    ∀ j, (feasMultiplier inst b ᵥ* inst.W) j ≤ 0 := by
  intro j
  have := hb.2.2 (Sum.inl j)
  rw [feasMul_W] at this
  simpa [feasCost] using this

theorem feas_cut_core (inst : Instance n1 n2 m1 m2 K)
    (hp : ∀ k, 0 < inst.p k) (x : Fin n1 → ℝ) :
    x ∈ K2 inst ↔ ∀ (k : Fin K) (b : FeasBasis n2 m2) (x' : Fin n1 → ℝ),
      IsFeasSimplexOptimal inst k b x' →
        (feasCutCoeffs inst k b).2 ≤ (feasCutCoeffs inst k b).1 ⬝ᵥ x := by
  rw [t1_mem_K2 inst hp]
  constructor
  · intro h k b x' hb
    rw [feasCut_iff]
    exact feasCut_valid inst k b (feas_dual_W inst k b x' hb) x (h k)
  · intro h k
    by_contra hnf
    obtain ⟨b, hb, hpos⟩ := feas_opt2 inst k x hnf
    have := (feasCut_iff inst k b x).mp (h k b x hb)
    linarith

def CutsInv (inst : Instance n1 n2 m1 m2 K) (s : State n1 K) : Prop :=
  (∀ c ∈ s.feasCuts, ∃ k b x'', IsFeasSimplexOptimal inst k b x'' ∧ c = feasCutCoeffs inst k b) ∧
  (∀ k, ∀ c ∈ s.optCuts k, ∃ b x'', IsSimplexOptimal inst k b x'' ∧ c = optCut inst k b)

lemma cutsInv_reach (inst : Instance n1 n2 m1 m2 K) (s : State n1 K) (hs : Reachable inst s) :
    CutsInv inst s := by
  classical
  induction hs with
  | refl => exact ⟨fun c hc => by simp [init] at hc, fun k c hc => by simp [init] at hc⟩
  | tail _ hst ih =>
    cases hst with
    | feas x θ k b hopt hfirst hpos hb =>
      refine ⟨fun c hc => ?_, ih.2⟩
      rcases List.mem_append.mp hc with hc | hc
      · exact ih.1 c hc
      · simp at hc; exact ⟨k, b, x, hb, hc⟩
    | opt x θ β hopt hfeas hβ hS =>
      refine ⟨ih.1, fun k c hc => ?_⟩
      dsimp only at hc
      split_ifs at hc
      · rcases List.mem_append.mp hc with hc | hc
        · exact ih.2 k c hc
        · simp at hc; exact ⟨β k, x, hβ k, hc⟩
      · exact ih.2 k c hc

theorem stop_core (inst : Instance n1 n2 m1 m2 K)
    (hp : ∀ k, 0 < inst.p k) (s : State n1 K) (hs : Reachable inst s)
    (x : Fin n1 → ℝ) (θ : Fin K → ℝ) (β : Fin K → Basis n2 m2)
    (hopt : IsMasterOptimal inst s x θ) (hfeas : ∀ k, feasLPValue inst k x = 0)
    (hβ : ∀ k, IsSimplexOptimal inst k (β k) x)
    (hstop : ∀ k, ¬ Cond14 inst s x θ k (β k)) :
    x ∈ K1 inst ∧ x ∈ K2 inst ∧ ∀ x' ∈ K1 inst, x' ∈ K2 inst → obj inst x ≤ obj inst x' := by
  classical
  have hinv := cutsInv_reach inst s hs
  set v : Fin K → ℝ := fun k => multiplier inst (β k) (inst.q k) ⬝ᵥ rr inst k x with hv
  have hQx : ∀ k, QVal inst x k = (v k : EReal) := fun k => (simplex_val inst k (β k) x (hβ k)).symm
  have hQ : Q inst x = ((∑ k, inst.p k * v k : ℝ) : EReal) := Q_coe inst x v hQx
  refine ⟨hopt.1.1, by rw [K2, Set.mem_setOf_eq, hQ]; exact EReal.coe_ne_top _, ?_⟩
  intro x' hx1 hx2
  have hsf := (t1_mem_K2 inst hp x').mp hx2
  have hQx'top : ∀ k, QVal inst x' k ≠ ⊤ := by
    intro k
    obtain ⟨y, hy, hW⟩ := hsf k
    exact ne_top_of_le_ne_top (EReal.coe_ne_top _) (QVal_le inst k x' y hy hW)
  have hQx'bot : ∀ k, QVal inst x' k ≠ ⊥ := fun k =>
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (QVal_ge_dual inst k x' _ (hβ k).2.2)
  set v' : Fin K → ℝ := fun k => (QVal inst x' k).toReal with hv'
  have hQx' : ∀ k, QVal inst x' k = (v' k : EReal) := fun k =>
    (EReal.coe_toReal (hQx'top k) (hQx'bot k)).symm
  have hQ' : Q inst x' = ((∑ k, inst.p k * v' k : ℝ) : EReal) := Q_coe inst x' v' hQx'
  set θ' : Fin K → ℝ := fun k => inst.p k * v' k with hθ'
  have hmf : MultiFeasible inst s.feasCuts s.optCuts x' θ' := by
    refine ⟨hx1, fun c hc => ?_, fun k c hc => ?_⟩
    · obtain ⟨k, b, x'', hb, rfl⟩ := hinv.1 c hc
      exact (feas_cut_core inst hp x').mp hx2 k b x'' hb
    · obtain ⟨b, x'', hb, rfl⟩ := hinv.2 k c hc
      have := (opt_cut_core inst k b x'' hb).1 x'
      rw [hQx' k, ← EReal.coe_mul, EReal.coe_le_coe_iff] at this
      simp only [θ']
      linarith
  have hle := hopt.2 x' θ' hmf
  have hne : ∀ k, s.optCuts k ≠ [] := fun k h => hstop k (Or.inl h)
  have hfilt : Finset.univ.filter (fun k => s.optCuts k ≠ []) = Finset.univ :=
    Finset.filter_true_of_mem (fun k _ => hne k)
  simp only [multiObj, hfilt] at hle
  have hθ : ∀ k, inst.p k * v k ≤ θ k := by
    intro k
    have := hstop k
    simp only [Cond14, not_or, not_lt] at this
    simpa [hv, rr] using this.2
  have hsum : ∑ k, inst.p k * v k ≤ ∑ k, θ k := Finset.sum_le_sum fun k _ => hθ k
  unfold obj
  rw [hQ, hQ', ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
  simp only [θ'] at hle
  linarith

-- MAIN_HERE

end MulticutLShaped.Bound

open MulticutLShaped.Bound


theorem solution {n1 n2 m1 m2 K : ℕ} (inst : Instance n1 n2 m1 m2 K)
    (hp : ∀ k, 0 < inst.p k) (x : Fin n1 → ℝ) :
    x ∈ K2 inst ↔ ∀ (k : Fin K) (b : FeasBasis n2 m2) (x' : Fin n1 → ℝ),
      IsFeasSimplexOptimal inst k b x' →
        (feasCutCoeffs inst k b).2 ≤ (feasCutCoeffs inst k b).1 ⬝ᵥ x := by
  exact feas_cut_core inst hp x
