-- Prove2me | solution 1 for HighOrderWalks.TwoSided.theorem_5_9
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-31T05:39:25.999151+00:00
-- url     : https://prove2.me/submissions/aef2bebc-0500-4ad9-b6a3-d4bb8479530e

import Mathlib
import Definitions.Def_HighOrderWalks_TwoSided_Setting
import Definitions.Def_HighOrderWalks_TwoSided_Subspaces

section

noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem mem_cells {X : Finset (Finset V)} {c : ℕ} {σ : Finset V} :
    σ ∈ cells X c ↔ σ ∈ X ∧ σ.card = c := by simp [cells]

omit [DecidableEq V] in
theorem supp_iff {X : Finset (Finset V)} {c : ℕ} {f : Finset V → ℝ} :
    Supp X c f ↔ ∀ σ, σ ∉ cells X c → f σ = 0 := by
  constructor
  · intro h σ hs
    by_contra hn
    exact hs (h σ hn)
  · intro h σ hn
    by_contra hs
    exact hn (h σ hs)

theorem dS_support {X : Finset (Finset V)} {c : ℕ} {f : Finset V → ℝ}
    (hf : Supp X c f) : Supp X (c + 1) (dS X f) := by
  rw [supp_iff]
  intro σ hσ
  unfold dS
  split_ifs with hx
  · apply Finset.sum_eq_zero
    intro τ hτ
    have ht := (Finset.mem_filter.mp hτ).2
    apply (supp_iff.mp hf) τ
    intro hc
    have hc' := mem_cells.mp hc
    exact hσ (mem_cells.mpr ⟨hx, by omega⟩)
  · rfl

theorem dStar_support {X : Finset (Finset V)} {m : Finset V → ℝ}
    {c : ℕ} {f : Finset V → ℝ} (hf : Supp X (c + 1) f) :
    Supp X c (dStar X m f) := by
  rw [supp_iff]
  intro τ hτ
  unfold dStar
  split_ifs with hx
  · apply Finset.sum_eq_zero
    intro σ hσ
    have hs := (Finset.mem_filter.mp hσ).2
    have hz : f σ = 0 := by
      apply (supp_iff.mp hf) σ
      intro hc
      have hc' := mem_cells.mp hc
      exact hτ (mem_cells.mpr ⟨hx, by omega⟩)
    rw [hz, mul_zero]
  · rfl

omit [DecidableEq V] in
theorem ip_symm (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (f g : Finset V → ℝ) : ip X m c f g = ip X m c g f := by
  unfold ip
  apply Finset.sum_congr rfl
  intro σ _
  ring

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open scoped BigOperators RealInnerProductSpace
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*}

abbrev CellSpace (X : Finset (Finset V)) (c : ℕ) :=
  EuclideanSpace ℝ ↥(cells X c)

def encode (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (f : Finset V → ℝ) : CellSpace X c :=
  WithLp.toLp 2 (fun σ => Real.sqrt (m σ) * f σ)

def decode (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (v : CellSpace X c) : Finset V → ℝ := by
  classical
  exact fun σ => if hs : σ ∈ cells X c then v ⟨σ, hs⟩ / Real.sqrt (m σ) else 0

theorem decode_support (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (v : CellSpace X c) : Supp X c (decode X m c v) := by
  classical
  rw [supp_iff]
  intro σ hs
  simp [decode, hs]

theorem encode_decode (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (hm : ∀ σ ∈ cells X c, 0 < m σ) (v : CellSpace X c) :
    encode X m c (decode X m c v) = v := by
  classical
  ext σ
  have hp : Real.sqrt (m σ) ≠ 0 := (Real.sqrt_pos.2 (hm σ σ.2)).ne'
  simp [encode, decode]
  field_simp [hp]

theorem decode_encode (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (hm : ∀ σ ∈ cells X c, 0 < m σ) (f : Finset V → ℝ) (hf : Supp X c f) :
    decode X m c (encode X m c f) = f := by
  classical
  funext σ
  by_cases hs : σ ∈ cells X c
  · have hp : Real.sqrt (m σ) ≠ 0 := (Real.sqrt_pos.2 (hm σ hs)).ne'
    simp [decode, encode, hs, hp]
  · simp [decode, hs, (supp_iff.mp hf) σ hs]

theorem encode_inner (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (hm : ∀ σ ∈ cells X c, 0 ≤ m σ) (f g : Finset V → ℝ) :
    inner ℝ (encode X m c f) (encode X m c g) = ip X m c f g := by
  classical
  simp only [encode, EuclideanSpace.inner_toLp_toLp, dotProduct, Pi.star_apply, star_trivial]
  rw [Finset.sum_coe_sort (cells X c)
    (fun σ => (Real.sqrt (m σ) * g σ) * (Real.sqrt (m σ) * f σ))]
  unfold ip
  apply Finset.sum_congr rfl
  intro σ hs
  have hsq := Real.sq_sqrt (hm σ hs)
  calc
    (Real.sqrt (m σ) * g σ) * (Real.sqrt (m σ) * f σ) =
        (Real.sqrt (m σ)) ^ 2 * f σ * g σ := by ring
    _ = _ := by rw [hsq]

theorem encode_norm (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (hm : ∀ σ ∈ cells X c, 0 ≤ m σ) (f : Finset V → ℝ) :
    ‖encode X m c f‖ = nrm X m c f := by
  unfold nrm
  rw [← encode_inner X m c hm f f, real_inner_self_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg _)]

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*}

def encodeLinear (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ) :
    (Finset V → ℝ) →ₗ[ℝ] CellSpace X c where
  toFun := encode X m c
  map_add' f g := by
    ext σ
    simp [encode, mul_add]
  map_smul' a f := by
    ext σ
    simp [encode, mul_left_comm]

def decodeLinear (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ) :
    CellSpace X c →ₗ[ℝ] (Finset V → ℝ) where
  toFun := decode X m c
  map_add' f g := by
    classical
    funext σ
    by_cases hs : σ ∈ cells X c <;> simp [decode, hs, add_div]
  map_smul' a f := by
    classical
    funext σ
    by_cases hs : σ ∈ cells X c <;> simp [decode, hs, mul_div_assoc]

def supportedModule (X : Finset (Finset V)) (c : ℕ) : Submodule ℝ (Finset V → ℝ) where
  carrier := {f | Supp X c f}
  zero_mem' := by
    change Supp X c 0
    rw [supp_iff]
    simp
  add_mem' := by
    intro f g hf hg
    change Supp X c f at hf
    change Supp X c g at hg
    change Supp X c (f + g)
    rw [supp_iff] at hf hg ⊢
    intro σ hs
    simp [hf σ hs, hg σ hs]
  smul_mem' := by
    intro a f hf
    change Supp X c f at hf
    change Supp X c (a • f)
    rw [supp_iff] at hf ⊢
    intro σ hs
    simp [hf σ hs]

def weightedEquiv (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (hm : ∀ σ ∈ cells X c, 0 < m σ) :
    supportedModule X c ≃ₗ[ℝ] CellSpace X c where
  toFun := fun f => encode X m c f
  invFun := fun v => ⟨decode X m c v, decode_support X m c v⟩
  left_inv f := by
    apply Subtype.ext
    exact decode_encode X m c hm f f.2
  right_inv := encode_decode X m c hm
  map_add' f g := (encodeLinear X m c).map_add f g
  map_smul' a f := (encodeLinear X m c).map_smul a f

def meanZeroSpace (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ) :
    Submodule ℝ (CellSpace X c) :=
  (Submodule.span ℝ {encode X m c (fun _ => 1)}).orthogonal

theorem encode_mem_meanZero (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (hm : ∀ σ ∈ cells X c, 0 ≤ m σ) (f : Finset V → ℝ) :
    encode X m c f ∈ meanZeroSpace X m c ↔ ip X m c f (fun _ => 1) = 0 := by
  rw [meanZeroSpace, Submodule.mem_orthogonal_singleton_iff_inner_left,
    encode_inner X m c hm]

end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*}

def meanFunctional (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ) :
    (Finset V → ℝ) →ₗ[ℝ] ℝ where
  toFun f := ip X m c f (fun _ => 1)
  map_add' f g := by simp [ip, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by simp [ip, Finset.mul_sum, mul_left_comm]

def c0Module (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ) :
    Submodule ℝ (Finset V → ℝ) := supportedModule X c ⊓ LinearMap.ker (meanFunctional X m c)

lemma mem_c0Module (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ) (f : Finset V → ℝ) :
    f ∈ c0Module X m c ↔ f ∈ C0 X m c := Iff.rfl

def c0WeightedEquiv (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (hm : ∀ σ ∈ cells X c, 0 < m σ) :
    c0Module X m c ≃ₗ[ℝ] meanZeroSpace X m c where
  toFun f := ⟨encode X m c f, (encode_mem_meanZero X m c (fun σ hσ => (hm σ hσ).le) f).2 f.2.2⟩
  invFun v := ⟨decode X m c v, decode_support X m c v, by
    apply (encode_mem_meanZero X m c (fun σ hσ => (hm σ hσ).le) _).1
    rw [encode_decode X m c hm]
    exact v.2⟩
  left_inv f := by
    apply Subtype.ext
    exact decode_encode X m c hm f f.2.1
  right_inv v := by
    apply Subtype.ext
    exact encode_decode X m c hm v
  map_add' f g := by
    apply Subtype.ext
    exact (encodeLinear X m c).map_add f g
  map_smul' a f := by
    apply Subtype.ext
    exact (encodeLinear X m c).map_smul a f

lemma c0WeightedEquiv_inner (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (hm : ∀ σ ∈ cells X c, 0 < m σ) (f g : c0Module X m c) :
    inner ℝ (c0WeightedEquiv X m c hm f) (c0WeightedEquiv X m c hm g) = ip X m c f g :=
  encode_inner X m c (fun σ hσ => (hm σ hσ).le) f g

lemma c0WeightedEquiv_norm (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (hm : ∀ σ ∈ cells X c, 0 < m σ) (f : c0Module X m c) :
    ‖c0WeightedEquiv X m c hm f‖ = nrm X m c f :=
  encode_norm X m c (fun σ hσ => (hm σ hσ).le) f

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem dS_cell {X : Finset (Finset V)} {c : ℕ} {σ : Finset V}
    (hσ : σ ∈ cells X (c + 1)) (f : Finset V → ℝ) :
    dS X f σ = ∑ τ ∈ cells X c, if τ ⊆ σ then f τ else 0 := by
  have h := mem_cells.mp hσ
  have he : X.filter (fun τ => τ ⊆ σ ∧ τ.card + 1 = σ.card) =
      (cells X c).filter (fun τ => τ ⊆ σ) := by
    ext τ
    simp [cells, h.2, and_comm]
    tauto
  simp only [dS, if_pos h.1, he, Finset.sum_filter]

theorem dStar_cell {X : Finset (Finset V)} {m : Finset V → ℝ}
    {c : ℕ} {τ : Finset V} (hτ : τ ∈ cells X c) (f : Finset V → ℝ) :
    dStar X m f τ = ∑ σ ∈ cells X (c + 1), if τ ⊆ σ then m σ / m τ * f σ else 0 := by
  have h := mem_cells.mp hτ
  have he : X.filter (fun σ => τ ⊆ σ ∧ σ.card = τ.card + 1) =
      (cells X (c + 1)).filter (fun σ => τ ⊆ σ) := by
    ext σ
    simp [cells, h.2, and_comm]
    tauto
  simp only [dStar, if_pos h.1, he, Finset.sum_filter]

theorem incidence_adjoint (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (hm : ∀ τ ∈ cells X c, m τ ≠ 0) (f g : Finset V → ℝ) :
    ip X m (c + 1) (dS X f) g = ip X m c f (dStar X m g) := by
  calc
    ip X m (c + 1) (dS X f) g =
        ∑ σ ∈ cells X (c + 1), ∑ τ ∈ cells X c,
          if τ ⊆ σ then m σ * f τ * g σ else 0 := by
      unfold ip
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [dS_cell hσ]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro τ _
      split_ifs <;> ring
    _ = ∑ τ ∈ cells X c, ∑ σ ∈ cells X (c + 1),
          if τ ⊆ σ then m σ * f τ * g σ else 0 := Finset.sum_comm
    _ = ip X m c f (dStar X m g) := by
      unfold ip
      apply Finset.sum_congr rfl
      intro τ hτ
      rw [dStar_cell hτ, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      split_ifs
      · field_simp [hm τ hτ]
      · ring

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

def dSLinear (X : Finset (Finset V)) : (Finset V → ℝ) →ₗ[ℝ] (Finset V → ℝ) where
  toFun := dS X
  map_add' f g := by
    funext σ
    by_cases hs : σ ∈ X <;> simp [dS, hs, Finset.sum_add_distrib]
  map_smul' a f := by
    funext σ
    simp [dS, Finset.mul_sum]

def dStarLinear (X : Finset (Finset V)) (m : Finset V → ℝ) :
    (Finset V → ℝ) →ₗ[ℝ] (Finset V → ℝ) where
  toFun := dStar X m
  map_add' f g := by
    funext σ
    by_cases hs : σ ∈ X <;> simp [dStar, hs, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext σ
    simp [dStar, Finset.mul_sum, mul_left_comm]

def upLinear (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ) :
    CellSpace X c →ₗ[ℝ] CellSpace X (c + 1) :=
  (encodeLinear X m (c + 1)).comp ((dSLinear X).comp (decodeLinear X m c))

def downLinear (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ) :
    CellSpace X (c + 1) →ₗ[ℝ] CellSpace X c :=
  (encodeLinear X m c).comp ((dStarLinear X m).comp (decodeLinear X m (c + 1)))

theorem up_encode (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (hm : ∀ σ ∈ cells X c, 0 < m σ) (f : Finset V → ℝ) (hf : Supp X c f) :
    upLinear X m c (encode X m c f) = encode X m (c + 1) (dS X f) := by
  change encode X m (c + 1) (dS X (decode X m c (encode X m c f))) = _
  rw [decode_encode X m c hm f hf]

theorem down_encode (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (hm : ∀ σ ∈ cells X (c + 1), 0 < m σ) (f : Finset V → ℝ)
    (hf : Supp X (c + 1) f) :
    downLinear X m c (encode X m (c + 1) f) = encode X m c (dStar X m f) := by
  change encode X m c (dStar X m (decode X m (c + 1) (encode X m (c + 1) f))) = _
  rw [decode_encode X m (c + 1) hm f hf]

theorem up_down_inner (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (hm : ∀ σ ∈ cells X c, 0 < m σ)
    (hm' : ∀ σ ∈ cells X (c + 1), 0 < m σ)
    (v : CellSpace X c) (w : CellSpace X (c + 1)) :
    inner ℝ (upLinear X m c v) w = inner ℝ v (downLinear X m c w) := by
  conv_lhs => rw [← encode_decode X m (c + 1) hm' w]
  conv_rhs => lhs; rw [← encode_decode X m c hm v]
  change inner ℝ (encode X m (c + 1) (dS X (decode X m c v)))
      (encode X m (c + 1) (decode X m (c + 1) w)) =
    inner ℝ (encode X m c (decode X m c v))
      (encode X m c (dStar X m (decode X m (c + 1) w)))
  rw [encode_inner X m (c + 1) (fun σ hσ => (hm' σ hσ).le),
    encode_inner X m c (fun σ hσ => (hm σ hσ).le)]
  exact incidence_adjoint X m c (fun σ hσ => (hm σ hσ).ne') _ _

end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh

lemma immediate_subfaces_card {V : Type*} [DecidableEq V]
    (X : Finset (Finset V)) (n : ℕ) (hX : IsPureComplex X n)
    (σ : Finset V) (hσ : σ ∈ X) (hne : σ.Nonempty) :
    (X.filter (fun τ => τ ⊆ σ ∧ τ.card + 1 = σ.card)).card = σ.card := by
  have hp : 0 < σ.card := Finset.card_pos.mpr hne
  have heq : X.filter (fun τ => τ ⊆ σ ∧ τ.card + 1 = σ.card) =
      σ.powersetCard (σ.card - 1) := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨_, hsub, hc⟩
      exact ⟨hsub, by omega⟩
    · rintro ⟨hsub, hc⟩
      exact ⟨hX.1 σ hσ τ hsub, hsub, by omega⟩
  rw [heq, Finset.card_powersetCard, Nat.choose_symm (by omega : 1 ≤ σ.card),
    Nat.choose_one_right]

lemma common_immediate_coface_eq_union {V : Type*} [DecidableEq V]
    (s t u : Finset V) (hst : s ≠ t) (hc : s.card = t.card)
    (hsu : s ⊆ u) (htu : t ⊆ u) (hu : u.card = s.card + 1) :
    u = s ∪ t := by
  have hsub : s ∪ t ⊆ u := Finset.union_subset hsu htu
  have hlo : s.card < (s ∪ t).card := by
    by_contra h
    have he : s = s ∪ t := Finset.eq_of_subset_of_card_le
      Finset.subset_union_left (by omega)
    have hts : t ⊆ s := by rw [he]; exact Finset.subset_union_right
    have heq : t = s := Finset.eq_of_subset_of_card_le hts (by omega)
    exact hst heq.symm
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

lemma common_immediate_subface_eq_inter {V : Type*} [DecidableEq V]
    (s t u : Finset V) (hst : s ≠ t) (hc : s.card = t.card)
    (hus : u ⊆ s) (hut : u ⊆ t) (hu : u.card + 1 = s.card) :
    u = s ∩ t := by
  have hsub : u ⊆ s ∩ t := Finset.subset_inter hus hut
  have hhi : (s ∩ t).card < s.card := by
    by_contra h
    have he : s ∩ t = s := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_left (by omega)
    have hst' : s ⊆ t := by rw [← he]; exact Finset.inter_subset_right
    have heq : s = t := Finset.eq_of_subset_of_card_le hst' (by omega)
    exact hst heq
  exact Finset.eq_of_subset_of_card_le hsub (by omega)

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem dS_one_cell {X : Finset (Finset V)} {n c : ℕ}
    (hX : IsPureComplex X n) {σ : Finset V} (hσ : σ ∈ cells X (c + 1)) :
    dS X (fun _ => 1) σ = (c + 1 : ℝ) := by
  have hs := mem_cells.mp hσ
  simp only [dS, if_pos hs.1, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [immediate_subfaces_card X n hX σ hs.1 (Finset.card_pos.mp (by omega)), hs.2]
  simp

theorem dStar_one_cell {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (hc : c ≤ n) {τ : Finset V} (hτ : τ ∈ cells X c) :
    dStar X m (fun _ => 1) τ = 1 := by
  have ht := mem_cells.mp hτ
  have he : X.filter (fun σ => τ ⊆ σ ∧ σ.card = τ.card + 1) =
      X.filter (fun σ => σ.card = τ.card + 1 ∧ τ ⊆ σ) := by
    ext σ
    simp only [Finset.mem_filter, and_comm]
  simp only [dStar, if_pos ht.1, mul_one, he]
  rw [← Finset.sum_div, ← hm.2 τ ht.1 (ht.2 ▸ hc)]
  exact div_self (hm.1 τ ht.1).ne'

omit [DecidableEq V] in
theorem ip_congr_right {X : Finset (Finset V)} {m : Finset V → ℝ} {c : ℕ}
    (f : Finset V → ℝ) {g h : Finset V → ℝ}
    (he : ∀ σ ∈ cells X c, g σ = h σ) : ip X m c f g = ip X m c f h := by
  unfold ip
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [he σ hσ]

theorem dS_mean {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (hc : c ≤ n) (f : Finset V → ℝ) :
    ip X m (c + 1) (dS X f) (fun _ => 1) = ip X m c f (fun _ => 1) := by
  rw [incidence_adjoint X m c (fun σ hσ => (hm.1 σ (mem_cells.mp hσ).1).ne')]
  exact ip_congr_right f (fun σ hσ => dStar_one_cell hm hc hσ)

theorem dStar_mean {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (f : Finset V → ℝ) :
    ip X m c (dStar X m f) (fun _ => 1) =
      (c + 1 : ℝ) * ip X m (c + 1) f (fun _ => 1) := by
  rw [ip_symm, ← incidence_adjoint X m c
    (fun σ hσ => (hm.1 σ (mem_cells.mp hσ).1).ne'), ip_symm]
  rw [ip_congr_right f (fun σ hσ => dS_one_cell hX hσ)]
  unfold ip
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

lemma dS_mem_c0 {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (hc : c ≤ n) {f : Finset V → ℝ} (hf : f ∈ c0Module X m c) :
    dS X f ∈ c0Module X m (c + 1) := by
  constructor
  · exact dS_support hf.1
  · change ip X m (c + 1) (dS X f) (fun _ => 1) = 0
    rw [dS_mean hm hc]
    exact hf.2

lemma iterate_mem_c0 {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (r : ℕ) (hr : c + r ≤ n + 1)
    {f : Finset V → ℝ} (hf : f ∈ c0Module X m c) :
    ((dSLinear X) ^ r) f ∈ c0Module X m (c + r) := by
  induction r with
  | zero => simpa using hf
  | succ r ih =>
      rw [Module.End.iterate_succ', LinearMap.comp_apply]
      change dS X (((dSLinear X) ^ r) f) ∈ c0Module X m (c + (r + 1))
      simpa only [Nat.add_assoc] using dS_mem_c0 (c := c + r) hm (by omega) (ih (by omega))

def imageLevel (X : Finset (Finset V)) (m : Finset V → ℝ) (k j : ℕ) :
    Submodule ℝ (Finset V → ℝ) :=
  (c0Module X m (j + 1)).map ((dSLinear X) ^ (k - j))

lemma imageLevel_le_c0 {X : Finset (Finset V)} {n k j : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (hk : k ≤ n) (hj : j ≤ k) :
    imageLevel X m k j ≤ c0Module X m (k + 1) := by
  rintro f ⟨g, hg, rfl⟩
  have h := iterate_mem_c0 hm (k - j) (by omega : j + 1 + (k - j) ≤ n + 1) hg
  have heq : j + 1 + (k - j) = k + 1 := by omega
  rwa [heq] at h

lemma imageLevel_mono {X : Finset (Finset V)} {n k j l : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (hk : k ≤ n) (hjl : j ≤ l) (hlk : l ≤ k) :
    imageLevel X m k j ≤ imageLevel X m k l := by
  rintro f ⟨g, hg, rfl⟩
  refine ⟨((dSLinear X) ^ (l - j)) g, ?_, ?_⟩
  · have h := iterate_mem_c0 hm (l - j) (by omega : j + 1 + (l - j) ≤ n + 1) hg
    have heq : j + 1 + (l - j) = l + 1 := by omega
    rwa [heq] at h
  · rw [← Module.End.mul_apply, ← pow_add]
    congr 2
    omega

def globalFlag (X : Finset (Finset V)) (m : Finset V → ℝ) (k j : ℕ) :
    Submodule ℝ (Finset V → ℝ) :=
  if j < k then imageLevel X m k j else c0Module X m (k + 1)

lemma globalFlag_le_c0 {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (hk : k ≤ n) (j : ℕ) :
    globalFlag X m k j ≤ c0Module X m (k + 1) := by
  unfold globalFlag
  split_ifs with h
  · exact imageLevel_le_c0 hm hk h.le
  · exact le_rfl

lemma globalFlag_mono {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (hk : k ≤ n) : Monotone (globalFlag X m k) := by
  intro i j hij
  unfold globalFlag
  split_ifs with hi hj
  · exact imageLevel_mono hm hk hij hj.le
  · exact imageLevel_le_c0 hm hk hi.le
  · omega
  · exact le_rfl

lemma imageLevel_native {X : Finset (Finset V)} {m : Finset V → ℝ} {k j : ℕ}
    (hk : k ≠ 0) (hj : j < k) :
    (imageLevel X m k j : Set (Finset V → ℝ)) = Vsp X m k j := by
  ext f
  change f ∈ imageLevel X m k j ↔ f ∈ Vsp X m k j
  simp only [Vsp, hk, ite_false, hj, ite_true, imageLevel, Submodule.mem_map,
    Module.End.pow_apply, Set.mem_image, mem_c0Module]
  rfl

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem decode_mean_zero {X : Finset (Finset V)} {m : Finset V → ℝ} {c : ℕ}
    (hm : ∀ σ ∈ cells X c, 0 < m σ) (v : meanZeroSpace X m c) :
    ip X m c (decode X m c v) (fun _ => 1) = 0 := by
  apply (encode_mem_meanZero X m c (fun σ hσ => (hm σ hσ).le) _).mp
  rw [encode_decode X m c hm]
  exact v.2

def upZero {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (hc : c ≤ n) :
    meanZeroSpace X m c →ₗ[ℝ] meanZeroSpace X m (c + 1) :=
  ((upLinear X m c).comp (meanZeroSpace X m c).subtype).codRestrict _ (by
    intro v
    change encode X m (c + 1) (dS X (decode X m c v)) ∈ meanZeroSpace X m (c + 1)
    rw [encode_mem_meanZero X m (c + 1)
      (fun σ hσ => (hm.1 σ (mem_cells.mp hσ).1).le), dS_mean hm hc]
    exact decode_mean_zero (fun σ hσ => hm.1 σ (mem_cells.mp hσ).1) v)

def downZero {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) :
    meanZeroSpace X m (c + 1) →ₗ[ℝ] meanZeroSpace X m c :=
  ((downLinear X m c).comp (meanZeroSpace X m (c + 1)).subtype).codRestrict _ (by
    intro v
    change encode X m c (dStar X m (decode X m (c + 1) v)) ∈ meanZeroSpace X m c
    rw [encode_mem_meanZero X m c
      (fun σ hσ => (hm.1 σ (mem_cells.mp hσ).1).le), dStar_mean hX hm,
      decode_mean_zero (fun σ hσ => hm.1 σ (mem_cells.mp hσ).1) v, mul_zero])

theorem upZero_downZero_inner {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hc : c ≤ n)
    (v : meanZeroSpace X m c) (w : meanZeroSpace X m (c + 1)) :
    inner ℝ (upZero hm hc v) w = inner ℝ v (downZero hX hm w) := by
  change inner ℝ (upLinear X m c v) (w : CellSpace X (c + 1)) =
    inner ℝ (v : CellSpace X c) (downLinear X m c w)
  exact up_down_inner X m c (fun σ hσ => hm.1 σ (mem_cells.mp hσ).1)
    (fun σ hσ => hm.1 σ (mem_cells.mp hσ).1) v w

end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open scoped BigOperators
namespace HighOrderWalks.TwoSided.Fresh
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma orthogonal_sum_sq (v : ι → E)
    (hv : ∀ i j, i ≠ j → inner ℝ (v i) (v j) = 0) :
    ‖∑ i, v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_sum]
  rw [Finset.sum_eq_single i]
  · exact real_inner_self_eq_norm_sq (v i)
  · intro j hj hji
    exact hv i j (Ne.symm hji)
  · simp

lemma orthogonal_sum_smul_sq (v : ι → E) (a : ι → ℝ)
    (hv : ∀ i j, i ≠ j → inner ℝ (v i) (v j) = 0) :
    ‖∑ i, a i • v i‖ ^ 2 = ∑ i, (a i) ^ 2 * ‖v i‖ ^ 2 := by
  rw [orthogonal_sum_sq]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  · intro i j hij
    simp only [real_inner_smul_left, real_inner_smul_right, hv i j hij, mul_zero]

lemma sum_norm_le_sqrt_card (v : ι → E)
    (hv : ∀ i j, i ≠ j → inner ℝ (v i) (v j) = 0) :
    ∑ i, ‖v i‖ ≤ Real.sqrt (Fintype.card ι : ℝ) * ‖∑ i, v i‖ := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (fun _ : ι => (1 : ℝ)) (fun i => ‖v i‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at h
  rw [← orthogonal_sum_sq v hv] at h
  have hs := Real.sq_sqrt (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ _)
  have hn : 0 ≤ Real.sqrt (Fintype.card ι : ℝ) * ‖∑ i, v i‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [sq_nonneg ((∑ i, ‖v i‖) - Real.sqrt (Fintype.card ι : ℝ) * ‖∑ i, v i‖)]

end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open scoped BigOperators
namespace HighOrderWalks.TwoSided.Fresh
variable (ι E : Type*) [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure OrthogonalBlocks where
  part : ι → E →ₗ[ℝ] E
  sum_part : ∀ x, ∑ i, part i x = x
  cross : ∀ i j, i ≠ j → ∀ x y, inner ℝ (part i x) (part j y) = 0

namespace OrthogonalBlocks
variable {ι E} (P : OrthogonalBlocks ι E)

lemma inner_part (i : ι) (x y : E) :
    inner ℝ (P.part i x) y = inner ℝ (P.part i x) (P.part i y) := by
  classical
  conv_lhs => rw [← P.sum_part y]
  rw [inner_sum, Finset.sum_eq_single i]
  · intro j hj hji
    exact P.cross i j (Ne.symm hji) x y
  · simp

lemma inner_part_self (i : ι) (x : E) :
    inner ℝ (P.part i x) x = ‖P.part i x‖ ^ 2 := by
  rw [P.inner_part, real_inner_self_eq_norm_sq]

lemma part_norm_le (i : ι) (x : E) : ‖P.part i x‖ ≤ ‖x‖ := by
  have h := real_inner_le_norm (P.part i x) x
  rw [P.inner_part_self] at h
  nlinarith [norm_nonneg (P.part i x), norm_nonneg x]

lemma norm_sq (x : E) : ‖x‖ ^ 2 = ∑ i, ‖P.part i x‖ ^ 2 := by
  simpa only [P.sum_part] using orthogonal_sum_sq (fun i => P.part i x)
    (fun i j hij => P.cross i j hij x x)

lemma sum_norm (x : E) :
    ∑ i, ‖P.part i x‖ ≤ Real.sqrt (Fintype.card ι : ℝ) * ‖x‖ := by
  simpa only [P.sum_part] using sum_norm_le_sqrt_card (fun i => P.part i x)
    (fun i j hij => P.cross i j hij x x)

def diagonal (a : ι → ℝ) : E →ₗ[ℝ] E := ∑ i, a i • P.part i

lemma diagonal_apply (a : ι → ℝ) (x : E) :
    P.diagonal a x = ∑ i, a i • P.part i x := by
  simp only [diagonal, LinearMap.sum_apply, LinearMap.smul_apply]

lemma diagonal_sq (a : ι → ℝ) (x : E) :
    ‖P.diagonal a x‖ ^ 2 = ∑ i, (a i) ^ 2 * ‖P.part i x‖ ^ 2 := by
  rw [P.diagonal_apply, orthogonal_sum_smul_sq]
  intro i j hij
  exact P.cross i j hij x x

lemma diagonal_inner (a : ι → ℝ) (x : E) :
    inner ℝ (P.diagonal a x) x = ∑ i, a i * ‖P.part i x‖ ^ 2 := by
  simp only [P.diagonal_apply, sum_inner, real_inner_smul_left, P.inner_part_self]

lemma diagonal_residual (A : E →ₗ[ℝ] E) (a : ι → ℝ) {e : ℝ} (he : 0 ≤ e)
    (hA : ∀ i x, ‖A (P.part i x) - a i • P.part i x‖ ≤ e * ‖P.part i x‖)
    (x : E) :
    ‖A x - P.diagonal a x‖ ≤ Real.sqrt (Fintype.card ι : ℝ) * e * ‖x‖ := by
  have hid : A x - P.diagonal a x =
      ∑ i, (A (P.part i x) - a i • P.part i x) := by
    rw [Finset.sum_sub_distrib, ← map_sum, P.sum_part, P.diagonal_apply]
  rw [hid]
  calc
    ‖∑ i, (A (P.part i x) - a i • P.part i x)‖ ≤
        ∑ i, ‖A (P.part i x) - a i • P.part i x‖ := norm_sum_le _ _
    _ ≤ ∑ i, e * ‖P.part i x‖ := Finset.sum_le_sum (fun i _ => hA i x)
    _ = e * ∑ i, ‖P.part i x‖ := (Finset.mul_sum ..).symm
    _ ≤ e * (Real.sqrt (Fintype.card ι : ℝ) * ‖x‖) := mul_le_mul_of_nonneg_left (P.sum_norm x) he
    _ = Real.sqrt (Fintype.card ι : ℝ) * e * ‖x‖ := by ring

end OrthogonalBlocks
end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open scoped BigOperators
namespace HighOrderWalks.TwoSided.Fresh
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def blocksOfSubspaces (U : ι → Submodule ℝ E)
    (hU : OrthogonalFamily ℝ (fun i => U i) (fun i => (U i).subtypeₗᵢ))
    (htop : iSup U = ⊤) : OrthogonalBlocks ι E where
  part i := (U i).starProjection.toLinearMap
  sum_part x := hU.sum_projection_of_mem_iSup x (htop ▸ Submodule.mem_top)
  cross i j hij x y := hU hij ((U i).orthogonalProjectionOnto x) ((U j).orthogonalProjectionOnto y)

lemma blocksOfSubspaces_part (U : ι → Submodule ℝ E)
    (hU : OrthogonalFamily ℝ (fun i => U i) (fun i => (U i).subtypeₗᵢ))
    (htop : iSup U = ⊤) (i : ι) (x : E) :
    (blocksOfSubspaces U hU htop).part i x = (U i).starProjection x := rfl

lemma blocksOfSubspaces_mem (U : ι → Submodule ℝ E)
    (hU : OrthogonalFamily ℝ (fun i => U i) (fun i => (U i).subtypeₗᵢ))
    (htop : iSup U = ⊤) (i : ι) (x : E) :
    (blocksOfSubspaces U hU htop).part i x ∈ U i :=
  (U i).starProjection_apply_mem x

lemma blocksOfSubspaces_unique (U : ι → Submodule ℝ E)
    (hU : OrthogonalFamily ℝ (fun i => U i) (fun i => (U i).subtypeₗᵢ))
    (htop : iSup U = ⊤) (i : ι) {x u : E}
    (hu : u ∈ U i) (horth : ∀ v ∈ U i, inner ℝ (x - u) v = 0) :
    (blocksOfSubspaces U hU htop).part i x = u :=
  (U i).eq_starProjection_of_mem_of_inner_eq_zero hu horth

end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
namespace HighOrderWalks.TwoSided.Fresh
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def flagPiece (F : ℕ → Submodule ℝ E) : ℕ → Submodule ℝ E
  | 0 => F 0
  | j + 1 => F (j + 1) ⊓ (F j)ᗮ

omit [FiniteDimensional ℝ E] in
lemma flagPiece_le (F : ℕ → Submodule ℝ E) (i : ℕ) : flagPiece F i ≤ F i := by
  cases i with
  | zero => exact le_rfl
  | succ i => exact inf_le_left

lemma flagPiece_partial_span (F : ℕ → Submodule ℝ E) (hF : Monotone F) (j : ℕ) :
    (⨆ i ≤ j, flagPiece F i) = F j := by
  induction j with
  | zero => simp [flagPiece]
  | succ j ih =>
      rw [Nat.iSup_le_succ, ih]
      change F j ⊔ (F (j + 1) ⊓ (F j)ᗮ) = F (j + 1)
      rw [inf_comm]
      exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (hF (by omega))

omit [FiniteDimensional ℝ E] in
lemma flagPiece_inner_zero_of_lt (F : ℕ → Submodule ℝ E) (hF : Monotone F)
    {i j : ℕ} (hij : i < j) {x y : E}
    (hx : x ∈ flagPiece F i) (hy : y ∈ flagPiece F j) : inner ℝ x y = 0 := by
  cases j with
  | zero => omega
  | succ j =>
      have hx' : x ∈ F j := hF (by omega) (flagPiece_le F i hx)
      have hy' : y ∈ (F j)ᗮ := hy.2
      exact Submodule.inner_right_of_mem_orthogonal hx' hy'

omit [FiniteDimensional ℝ E] in
lemma flagPiece_inner_zero (F : ℕ → Submodule ℝ E) (hF : Monotone F)
    {i j : ℕ} (hij : i ≠ j) {x y : E}
    (hx : x ∈ flagPiece F i) (hy : y ∈ flagPiece F j) : inner ℝ x y = 0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact flagPiece_inner_zero_of_lt F hF h hx hy
  · rw [real_inner_comm]
    exact flagPiece_inner_zero_of_lt F hF h hy hx

lemma flagPiece_total_span (F : ℕ → Submodule ℝ E) (hF : Monotone F)
    (r : ℕ) (htop : F r = ⊤) : (⨆ i : Fin (r + 1), flagPiece F i.val) = ⊤ := by
  rw [← htop, ← flagPiece_partial_span F hF r]
  apply le_antisymm
  · refine iSup_le fun i => ?_
    exact le_iSup_of_le i.val (le_iSup_of_le (by omega : i.val ≤ r) le_rfl)
  · refine iSup_le fun i => iSup_le fun hi => ?_
    exact le_iSup_of_le (⟨i, by omega⟩ : Fin (r + 1)) le_rfl

end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open scoped BigOperators
namespace HighOrderWalks.TwoSided.Fresh
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma flagPiece_orthogonalFamily (F : ℕ → Submodule ℝ E) (hF : Monotone F) (r : ℕ) :
    OrthogonalFamily ℝ (fun i : Fin (r + 1) => flagPiece F i.val)
      (fun i => (flagPiece F i.val).subtypeₗᵢ) := by
  intro i j hij x y
  exact flagPiece_inner_zero F hF (fun h => hij (Fin.ext h)) x.2 y.2

def flagBlocks (F : ℕ → Submodule ℝ E) (hF : Monotone F) (r : ℕ) (htop : F r = ⊤) :
    OrthogonalBlocks (Fin (r + 1)) E :=
  blocksOfSubspaces (fun i => flagPiece F i.val) (flagPiece_orthogonalFamily F hF r)
    (flagPiece_total_span F hF r htop)

lemma flagBlocks_mem (F : ℕ → Submodule ℝ E) (hF : Monotone F) (r : ℕ) (htop : F r = ⊤)
    (i : Fin (r + 1)) (x : E) : (flagBlocks F hF r htop).part i x ∈ F i.val :=
  flagPiece_le F i.val ((flagPiece F i.val).starProjection_apply_mem x)

lemma flagBlocks_zero_above (F : ℕ → Submodule ℝ E) (hF : Monotone F) (r : ℕ) (htop : F r = ⊤)
    (i : Fin (r + 1)) {j : ℕ} {x : E} (hx : x ∈ F j) (hji : j < i.val) :
    (flagBlocks F hF r htop).part i x = 0 := by
  change (flagPiece F i.val).starProjection x = 0
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _)
  intro w hw
  rw [sub_zero]
  obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i.val ≠ 0)
  rw [hl] at hw
  have hx' : x ∈ F l := hF (by omega) hx
  exact Submodule.inner_right_of_mem_orthogonal hx' hw.2

end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

def decodeZeroLinear (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ) :
    meanZeroSpace X m c →ₗ[ℝ] (Finset V → ℝ) :=
  (decodeLinear X m c).comp (meanZeroSpace X m c).subtype

def levelFlag (X : Finset (Finset V)) (m : Finset V → ℝ) (k j : ℕ) :
    Submodule ℝ (meanZeroSpace X m (k + 1)) :=
  (globalFlag X m k j).comap (decodeZeroLinear X m (k + 1))

lemma mem_levelFlag (X : Finset (Finset V)) (m : Finset V → ℝ) (k j : ℕ)
    (v : meanZeroSpace X m (k + 1)) :
    v ∈ levelFlag X m k j ↔ decode X m (k + 1) v ∈ globalFlag X m k j := Iff.rfl

lemma levelFlag_mono {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (hk : k ≤ n) : Monotone (levelFlag X m k) := by
  intro i j hij
  exact Submodule.comap_mono (globalFlag_mono hm hk hij)

lemma levelFlag_top {X : Finset (Finset V)} {n : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (k : ℕ) : levelFlag X m k k = ⊤ := by
  apply top_unique
  intro v hv
  change decode X m (k + 1) v ∈ globalFlag X m k k
  simp only [globalFlag, lt_self_iff_false, ite_false]
  exact ⟨decode_support X m (k + 1) v,
    decode_mean_zero (fun σ hσ => hm.1 σ (mem_cells.mp hσ).1) v⟩

lemma levelFlag_native {X : Finset (Finset V)} {m : Finset V → ℝ} {k j : ℕ}
    (hk : k ≠ 0) (hj : j < k) (v : meanZeroSpace X m (k + 1)) :
    v ∈ levelFlag X m k j ↔ decode X m (k + 1) v ∈ Vsp X m k j := by
  rw [mem_levelFlag]
  simp only [globalFlag, hj, ite_true]
  exact Set.ext_iff.mp (imageLevel_native hk hj) _

noncomputable def nativeFlagBlocks {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (hk : k ≤ n) :
    OrthogonalBlocks (Fin (k + 1)) (meanZeroSpace X m (k + 1)) :=
  flagBlocks (levelFlag X m k) (levelFlag_mono hm hk) k (levelFlag_top hm k)

end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

lemma globalFlag_eq_image {X : Finset (Finset V)} {m : Finset V → ℝ} {k j : ℕ}
    (hj : j ≤ k) : globalFlag X m k j = imageLevel X m k j := by
  unfold globalFlag
  split_ifs with h
  · rfl
  · have heq : j = k := by omega
    subst j
    simp only [imageLevel, Nat.sub_self, pow_zero]
    exact (Submodule.map_id _).symm

lemma globalFlag_succ {X : Finset (Finset V)} {m : Finset V → ℝ} {k j : ℕ}
    (hj : j ≤ k) :
    globalFlag X m (k + 1) j = (globalFlag X m k j).map (dSLinear X) := by
  rw [globalFlag_eq_image (by omega : j ≤ k + 1), globalFlag_eq_image hj]
  unfold imageLevel
  rw [← Submodule.map_comp]
  have hpow : k + 1 - j = (k - j) + 1 := by omega
  rw [hpow, Module.End.iterate_succ']

lemma decode_upZero {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (hc : c ≤ n) (v : meanZeroSpace X m c) :
    decode X m (c + 1) (upZero hm hc v) = dS X (decode X m c v) := by
  change decode X m (c + 1) (encode X m (c + 1) (dS X (decode X m c v))) = _
  exact decode_encode X m (c + 1) (fun σ hσ => hm.1 σ (mem_cells.mp hσ).1) _
    (dS_support (decode_support X m c v))

lemma levelFlag_succ {X : Finset (Finset V)} {n k j : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (hk : k + 1 ≤ n) (hj : j ≤ k) :
    levelFlag X m (k + 1) j = (levelFlag X m k j).map (upZero hm hk) := by
  ext u
  rw [mem_levelFlag, globalFlag_succ hj, Submodule.mem_map, Submodule.mem_map]
  constructor
  · rintro ⟨f, hf, he⟩
    have hf0 := globalFlag_le_c0 hm (by omega : k ≤ n) j hf
    let v := c0WeightedEquiv X m (k + 1) (fun σ hσ => hm.1 σ (mem_cells.mp hσ).1) ⟨f, hf0⟩
    have hd : decode X m (k + 1) v = f :=
      decode_encode X m (k + 1) (fun σ hσ => hm.1 σ (mem_cells.mp hσ).1) f hf0.1
    refine ⟨v, ?_, ?_⟩
    · rw [mem_levelFlag, hd]
      exact hf
    · apply Subtype.ext
      change encode X m (k + 1 + 1) (dS X (decode X m (k + 1) v)) = (u : CellSpace X (k + 1 + 1))
      rw [hd]
      change dS X f = decode X m (k + 1 + 1) u at he
      rw [he, encode_decode X m (k + 1 + 1) (fun σ hσ => hm.1 σ (mem_cells.mp hσ).1)]
  · rintro ⟨v, hv, rfl⟩
    exact ⟨decode X m (k + 1) v, hv, (decode_upZero hm hk v).symm⟩

end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*}

lemma decode_inner (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (hm : ∀ σ ∈ cells X c, 0 < m σ) (v w : meanZeroSpace X m c) :
    ip X m c (decode X m c v) (decode X m c w) = inner ℝ v w := by
  rw [← encode_inner X m c (fun σ hσ => (hm σ hσ).le),
    encode_decode X m c hm, encode_decode X m c hm]
  rfl

lemma decodeZero_injective (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (hm : ∀ σ ∈ cells X c, 0 < m σ) :
    Function.Injective (fun v : meanZeroSpace X m c => decode X m c v) := by
  intro v w h
  apply Subtype.ext
  have he := congrArg (encode X m c) h
  simpa only [encode_decode X m c hm] using he

lemma decode_zero_eq_zero (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ) :
    decode X m c (0 : meanZeroSpace X m c) = 0 := by
  exact (decodeLinear X m c).map_zero

variable [DecidableEq V]
lemma decode_downZero {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (v : meanZeroSpace X m (c + 1)) :
    decode X m c (downZero hX hm v) = dStar X m (decode X m (c + 1) v) := by
  change decode X m c (encode X m c (dStar X m (decode X m (c + 1) v))) = _
  exact decode_encode X m c (fun σ hσ => hm.1 σ (mem_cells.mp hσ).1) _
    (dStar_support (decode_support X m (c + 1) v))

lemma downZero_eq_zero_iff {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (v : meanZeroSpace X m (c + 1)) :
    downZero hX hm v = 0 ↔ ∀ τ ∈ cells X c, dStar X m (decode X m (c + 1) v) τ = 0 := by
  constructor
  · intro h τ hτ
    have he := congrArg (decode X m c ∘ Subtype.val) h
    rw [Function.comp_apply, Function.comp_apply, decode_downZero hX hm, decode_zero_eq_zero] at he
    exact congrFun he τ
  · intro h
    apply decodeZero_injective X m c (fun σ hσ => hm.1 σ (mem_cells.mp hσ).1)
    change decode X m c (downZero hX hm v) = decode X m c (0 : meanZeroSpace X m c)
    rw [decode_downZero hX hm, decode_zero_eq_zero]
    funext τ
    by_cases ht : τ ∈ cells X c
    · exact h τ ht
    · exact supp_iff.mp (dStar_support (decode_support X m (c + 1) v)) τ ht

end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh

lemma range_orthogonal_eq_kernel {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (D : E →ₗ[ℝ] F) (T : F →ₗ[ℝ] E)
    (hadj : ∀ v w, inner ℝ (D v) w = inner ℝ v (T w)) :
    (LinearMap.range D)ᗮ = LinearMap.ker T := by
  ext w
  rw [Submodule.mem_orthogonal, LinearMap.mem_ker]
  constructor
  · intro h
    have hz := h (D (T w)) (LinearMap.mem_range_self D (T w))
    rw [hadj, real_inner_self_eq_norm_sq] at hz
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (T w)])
  · intro h v hv
    obtain ⟨u, rfl⟩ := hv
    rw [hadj, h, inner_zero_right]

variable {V : Type*} [DecidableEq V]

lemma nativePiece_top_succ {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hk : k + 1 ≤ n) :
    flagPiece (levelFlag X m (k + 1)) (k + 1) = LinearMap.ker (downZero (c := k + 1) hX hm) := by
  rw [flagPiece, levelFlag_top hm, top_inf_eq, levelFlag_succ hm hk le_rfl,
    levelFlag_top hm, Submodule.map_top]
  exact range_orthogonal_eq_kernel (upZero hm hk) (downZero hX hm)
    (upZero_downZero_inner hX hm hk)

lemma levelFlag_orthogonal_native {X : Finset (Finset V)} {n k j : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (hk : k ≤ n) (hk0 : k ≠ 0) (hj : j < k)
    (v : meanZeroSpace X m (k + 1)) :
    v ∈ (levelFlag X m k j)ᗮ ↔
      ∀ f ∈ Vsp X m k j, ip X m (k + 1) (decode X m (k + 1) v) f = 0 := by
  rw [Submodule.mem_orthogonal']
  constructor
  · intro h f hf
    have hfg : f ∈ globalFlag X m k j := by
      rw [globalFlag, if_pos hj]
      exact Set.ext_iff.mp (imageLevel_native hk0 hj).symm _ |>.mp hf
    have hf0 := globalFlag_le_c0 hm hk j hfg
    let w := c0WeightedEquiv X m (k + 1) (fun σ hσ => hm.1 σ (mem_cells.mp hσ).1) ⟨f, hf0⟩
    have hd : decode X m (k + 1) w = f :=
      decode_encode X m (k + 1) (fun σ hσ => hm.1 σ (mem_cells.mp hσ).1) f hf0.1
    have hw : w ∈ levelFlag X m k j := by rw [mem_levelFlag, hd]; exact hfg
    have hh := h w hw
    rw [← decode_inner X m (k + 1) (fun σ hσ => hm.1 σ (mem_cells.mp hσ).1), hd] at hh
    exact hh
  · intro h w hw
    have hh := h (decode X m (k + 1) w) ((levelFlag_native hk0 hj w).1 hw)
    rwa [decode_inner X m (k + 1) (fun σ hσ => hm.1 σ (mem_cells.mp hσ).1)] at hh

lemma nativePiece_decode_iff {X : Finset (Finset V)} {n k j : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hk : k ≤ n) (hj : j ≤ k)
    (v : meanZeroSpace X m (k + 1)) :
    v ∈ flagPiece (levelFlag X m k) j ↔ decode X m (k + 1) v ∈ Usp X m k j := by
  cases k with
  | zero =>
      have hj0 : j = 0 := by omega
      subst j
      simp only [flagPiece, levelFlag_top hm, Submodule.mem_top, Usp, Vsp, ite_true]
      exact iff_of_true trivial ⟨decode_support X m 1 v,
        decode_mean_zero (fun σ hσ => hm.1 σ (mem_cells.mp hσ).1) v⟩
  | succ k =>
      by_cases hj0 : j = 0
      · subst j
        simp only [flagPiece, Usp, ite_true]
        exact levelFlag_native (by omega) (by omega) v
      by_cases hjk : j < k + 1
      · obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
        change (v ∈ levelFlag X m (k + 1) (l + 1) ∧ v ∈ (levelFlag X m (k + 1) l)ᗮ) ↔ _
        rw [Usp, if_neg (Nat.succ_ne_zero l), if_pos hjk]
        simp only [Nat.succ_sub_one]
        rw [levelFlag_native (by omega) hjk,
          levelFlag_orthogonal_native hm hk (by omega) (by omega)]
        have hs := decode_support X m (k + 1 + 1) (v : CellSpace X (k + 1 + 1))
        change (_ ∧ _) ↔ (_ ∧ Supp X (k + 1 + 1) (decode X m (k + 1 + 1) v) ∧ _)
        tauto
      · have heq : j = k + 1 := by omega
        subst j
        rw [nativePiece_top_succ hX hm hk, LinearMap.mem_ker, downZero_eq_zero_iff hX hm]
        simp only [Usp, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
          lt_self_iff_false, Vsp]
        exact (and_iff_right (decode_support X m (k + 1 + 1) (v : CellSpace X (k + 1 + 1)))).symm

end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

def nativeEnergy {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hk : k + 1 ≤ n) :
    meanZeroSpace X m (k + 1) →ₗ[ℝ] meanZeroSpace X m (k + 1) :=
  (downZero hX hm).comp (upZero hm hk)

lemma nativeEnergy_inner {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hk : k + 1 ≤ n)
    (v w : meanZeroSpace X m (k + 1)) :
    inner ℝ (nativeEnergy hX hm hk v) w = inner ℝ (upZero hm hk v) (upZero hm hk w) := by
  change inner ℝ (downZero hX hm (upZero hm hk v)) w = _
  rw [real_inner_comm, ← upZero_downZero_inner hX hm hk, real_inner_comm]

lemma nativeEnergy_energy {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hk : k + 1 ≤ n)
    (v : meanZeroSpace X m (k + 1)) :
    inner ℝ (nativeEnergy hX hm hk v) v = ‖upZero hm hk v‖ ^ 2 := by
  rw [nativeEnergy_inner, real_inner_self_eq_norm_sq]

end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open scoped BigOperators
namespace HighOrderWalks.TwoSided.Fresh
namespace OrthogonalBlocks
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (P : OrthogonalBlocks ι E)

lemma shifted_diagonal (a : ι → ℝ) (μ : ℝ) (x : E) :
    μ • x - P.diagonal a x = P.diagonal (fun i => μ - a i) x := by
  rw [P.diagonal_apply, P.diagonal_apply]
  simp only [sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, P.sum_part]

lemma eigenvalue_near_diagonal (A : E →ₗ[ℝ] E) (a : ι → ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hA : ∀ x, ‖A x - P.diagonal a x‖ ≤ δ * ‖x‖)
    {μ : ℝ} {x : E} (hx : x ≠ 0) (heig : A x = μ • x) :
    ∃ i, |μ - a i| ≤ δ := by
  classical
  by_contra! hf
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hsome : ∃ i, 0 < ‖P.part i x‖ := by
    by_contra! hh
    have hz : ∀ i, P.part i x = 0 := fun i => norm_eq_zero.mp (le_antisymm (hh i) (norm_nonneg _))
    have := P.sum_part x
    simp only [hz, Finset.sum_const_zero] at this
    exact hx this.symm
  obtain ⟨i, hi⟩ := hsome
  have hle : ∀ j, δ ^ 2 * ‖P.part j x‖ ^ 2 ≤ (μ - a j) ^ 2 * ‖P.part j x‖ ^ 2 := by
    intro j
    have h := hf j
    have hs : δ ^ 2 ≤ (μ - a j) ^ 2 := by nlinarith [sq_abs (μ - a j)]
    exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)
  have hlt : δ ^ 2 * ‖P.part i x‖ ^ 2 < (μ - a i) ^ 2 * ‖P.part i x‖ ^ 2 := by
    have hs : δ ^ 2 < (μ - a i) ^ 2 := by nlinarith [hf i, sq_abs (μ - a i)]
    exact mul_lt_mul_of_pos_right hs (sq_pos_of_pos hi)
  have hh := Finset.sum_lt_sum (s := Finset.univ) (fun j _ => hle j) ⟨i, Finset.mem_univ _, hlt⟩
  rw [← Finset.mul_sum, ← P.norm_sq, ← P.diagonal_sq] at hh
  have hb := hA x
  rw [heig, P.shifted_diagonal] at hb
  nlinarith [norm_nonneg (P.diagonal (fun j => μ - a j) x)]

lemma remainder_sq (j : ι) (x : E) :
    ‖x - P.part j x‖ ^ 2 = ‖x‖ ^ 2 - ‖P.part j x‖ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_comm, P.inner_part_self]
  ring

lemma complementary_bound (a : ι → ℝ) (j : ι) (μ : ℝ) (x : E)
    {g : ℝ} (hg : 0 ≤ g) (hgap : ∀ i, i ≠ j → g ≤ |μ - a i|) :
    g * ‖x - P.part j x‖ ≤ ‖μ • x - P.diagonal a x‖ := by
  classical
  have hh : ∀ i, g ^ 2 * ‖P.part i x‖ ^ 2 ≤
      (μ - a i) ^ 2 * ‖P.part i x‖ ^ 2 + if i = j then g ^ 2 * ‖P.part j x‖ ^ 2 else 0 := by
    intro i
    by_cases hij : i = j
    · subst i
      simp only [ite_true]
      nlinarith [mul_nonneg (sq_nonneg (μ - a j)) (sq_nonneg ‖P.part j x‖)]
    · simp only [hij, ite_false, add_zero]
      have hs : g ^ 2 ≤ (μ - a i) ^ 2 := by nlinarith [hgap i hij, sq_abs (μ - a i)]
      exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hh i)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hs
  rw [← Finset.mul_sum, ← P.norm_sq, ← P.diagonal_sq] at hs
  rw [P.shifted_diagonal]
  have hr := P.remainder_sq j x
  nlinarith [norm_nonneg (P.diagonal (fun i => μ - a i) x),
    mul_nonneg hg (norm_nonneg (x - P.part j x))]

end OrthogonalBlocks
end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open scoped BigOperators
namespace HighOrderWalks.TwoSided.Fresh
namespace OrthogonalBlocks
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (P : OrthogonalBlocks ι E)

def blockSum (s : Finset ι) : E →ₗ[ℝ] E := ∑ i ∈ s, P.part i

lemma partial_apply (s : Finset ι) (x : E) :
    P.blockSum s x = ∑ i ∈ s, P.part i x := by
  simp only [blockSum, LinearMap.sum_apply]

lemma inner_diagonal_part (a : ι → ℝ) (x : E) (j : ι) :
    inner ℝ (P.diagonal a x) (P.part j x) = a j * ‖P.part j x‖ ^ 2 := by
  classical
  rw [P.diagonal_apply, sum_inner, Finset.sum_eq_single j]
  · rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
  · intro i hi hij
    rw [real_inner_smul_left, P.cross i j hij, mul_zero]
  · simp

lemma inner_diagonal_partial (a : ι → ℝ) (s : Finset ι) (x : E) :
    inner ℝ (P.diagonal a x) (P.blockSum s x) = ∑ i ∈ s, a i * ‖P.part i x‖ ^ 2 := by
  simp only [P.partial_apply, inner_sum, P.inner_diagonal_part]

lemma partial_sq (s : Finset ι) (x : E) :
    ‖P.blockSum s x‖ ^ 2 = ∑ i ∈ s, ‖P.part i x‖ ^ 2 := by
  classical
  rw [P.partial_apply, ← real_inner_self_eq_norm_sq, sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_sum, Finset.sum_eq_single i]
  · exact real_inner_self_eq_norm_sq (P.part i x)
  · intro j hj hji
    exact P.cross i j (Ne.symm hji) x x
  · exact fun h => False.elim (h hi)

lemma diagonal_lower_partial (a : ι → ℝ) (s : Finset ι) (ha : ∀ i ∈ s, 1 ≤ a i) (x : E) :
    ‖P.blockSum s x‖ ^ 2 ≤ inner ℝ (P.diagonal a x) (P.blockSum s x) := by
  rw [P.partial_sq, P.inner_diagonal_partial]
  exact Finset.sum_le_sum (fun i hi => by nlinarith [sq_nonneg ‖P.part i x‖, ha i hi])

lemma diagonal_partial_residual (a : ι → ℝ) (s : Finset ι) (c : ℝ) (x : E)
    {K : ℝ} (hK : 0 ≤ K) (ha : ∀ i ∈ s, |a i - c| ≤ K)
    (hz : ∀ i, i ∉ s → (a i - c) • P.part i x = 0) :
    ‖P.diagonal a x - c • x‖ ≤ K * ‖P.blockSum s x‖ := by
  classical
  have hid : P.diagonal a x - c • x = P.diagonal (fun i => a i - c) x := by
    simp only [P.diagonal_apply, sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, P.sum_part]
  have hs : ∑ i, (a i - c) ^ 2 * ‖P.part i x‖ ^ 2 =
      ∑ i ∈ s, (a i - c) ^ 2 * ‖P.part i x‖ ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i hi hni
    have h := congrArg (fun v : E => ‖v‖ ^ 2) (hz i hni)
    simpa only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_zero, zero_pow (by decide : 2 ≠ 0)] using h
  have hle : ∑ i ∈ s, (a i - c) ^ 2 * ‖P.part i x‖ ^ 2 ≤
      K ^ 2 * ∑ i ∈ s, ‖P.part i x‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hsq : (a i - c) ^ 2 ≤ K ^ 2 := by
      have hh := mul_le_mul (ha i hi) (ha i hi) (abs_nonneg (a i - c)) hK
      nlinarith [sq_abs (a i - c)]
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  rw [← P.partial_sq, ← hs, ← P.diagonal_sq] at hle
  rw [hid]
  nlinarith [norm_nonneg (P.diagonal (fun i => a i - c) x),
    mul_nonneg hK (norm_nonneg (P.blockSum s x))]

end OrthogonalBlocks
end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open scoped BigOperators
namespace HighOrderWalks.TwoSided.Fresh
namespace OrthogonalBlocks
variable {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable (P : OrthogonalBlocks ι E)

lemma diagonal_inner_bounds (a : ι → ℝ) {K : ℝ}
    (ha : ∀ i, 1 ≤ a i ∧ a i ≤ K) (x : E) :
    ‖x‖ ^ 2 ≤ inner ℝ (P.diagonal a x) x ∧
      inner ℝ (P.diagonal a x) x ≤ K * ‖x‖ ^ 2 := by
  rw [P.diagonal_inner, P.norm_sq, Finset.mul_sum]
  constructor
  · exact Finset.sum_le_sum (fun i _ => by nlinarith [sq_nonneg ‖P.part i x‖, (ha i).1])
  · exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (ha i).2 (sq_nonneg _))

lemma near_diagonal_energy (A : E →ₗ[ℝ] E) (a : ι → ℝ) {K δ : ℝ}
    (ha : ∀ i, 1 ≤ a i ∧ a i ≤ K)
    (herr : ∀ x, ‖A x - P.diagonal a x‖ ≤ δ * ‖x‖) (x : E) :
    (1 - δ) * ‖x‖ ^ 2 ≤ inner ℝ (A x) x ∧
      inner ℝ (A x) x ≤ (K + δ) * ‖x‖ ^ 2 := by
  have he := abs_real_inner_le_norm (A x - P.diagonal a x) x
  rw [inner_sub_left] at he
  have hh := mul_le_mul_of_nonneg_right (herr x) (norm_nonneg x)
  obtain ⟨hl, hu⟩ := P.diagonal_inner_bounds a ha x
  obtain ⟨hneg, hpos⟩ := abs_le.mp (he.trans hh)
  constructor <;> nlinarith

lemma map_energy_bounds (D : E →ₗ[ℝ] F) (A : E →ₗ[ℝ] E) (a : ι → ℝ)
    {K δ : ℝ} (hK : 1 ≤ K) (hδ : δ ≤ 1 / 2)
    (ha : ∀ i, 1 ≤ a i ∧ a i ≤ K)
    (herr : ∀ x, ‖A x - P.diagonal a x‖ ≤ δ * ‖x‖)
    (henergy : ∀ x, inner ℝ (A x) x = ‖D x‖ ^ 2) (x : E) :
    ‖x‖ ≤ 2 * ‖D x‖ ∧ ‖D x‖ ≤ (K + 1) * ‖x‖ := by
  obtain ⟨hl, hu⟩ := P.near_diagonal_energy A a ha herr x
  rw [henergy] at hl hu
  have hh : (1 / 2 : ℝ) * ‖x‖ ^ 2 ≤ (1 - δ) * ‖x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have hk : K + δ ≤ (K + 1) ^ 2 := by nlinarith
  have hk' := mul_le_mul_of_nonneg_right hk (sq_nonneg ‖x‖)
  constructor
  · nlinarith [norm_nonneg x, norm_nonneg (D x)]
  · have hp : 0 ≤ (K + 1) * ‖x‖ := mul_nonneg (by linarith) (norm_nonneg x)
    nlinarith [norm_nonneg (D x)]

end OrthogonalBlocks
end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open scoped BigOperators
namespace HighOrderWalks.TwoSided.Fresh
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma low_component_bound (A B : E →ₗ[ℝ] E) (v w : E) {δ : ℝ}
    (herr : ‖A v - B v‖ ≤ δ * ‖v‖)
    (horth : inner ℝ (A v) w = 0)
    (hpos : ‖w‖ ^ 2 ≤ inner ℝ (B v) w) : ‖w‖ ≤ δ * ‖v‖ := by
  have he := real_inner_le_norm (B v - A v) w
  rw [inner_sub_left, horth, sub_zero, norm_sub_rev] at he
  have hh := mul_le_mul_of_nonneg_right herr (norm_nonneg w)
  by_cases hw : ‖w‖ = 0
  · rw [hw]
    exact (norm_nonneg _).trans herr
  · have hp : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hw)
    nlinarith

namespace OrthogonalBlocks
variable {ι : Type*} [Fintype ι] (P : OrthogonalBlocks ι E)

lemma raise_from_flag (D : E →ₗ[ℝ] F) (A : E →ₗ[ℝ] E) (a : ι → ℝ)
    (v : E) (s : Finset ι) (c : ℝ) {δ K L R : ℝ}
    (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hL : 0 ≤ L) (_hR : 0 ≤ R)
    (herr : ‖A v - P.diagonal a v‖ ≤ δ * ‖v‖)
    (ha : ∀ i ∈ s, 1 ≤ a i)
    (hcoeff : ∀ i ∈ s, |a i - c| ≤ K)
    (hzero : ∀ i, i ∉ s → (a i - c) • P.part i v = 0)
    (horth : inner ℝ (A v) (P.blockSum s v) = 0)
    (hD : ∀ x, ‖D x‖ ≤ L * ‖x‖)
    (hcoerc : ‖v‖ ≤ R * ‖D v‖) :
    ‖D (A v) - c • D v‖ ≤ L * (1 + K) * δ * R * ‖D v‖ := by
  have hw := low_component_bound A (P.diagonal a) v (P.blockSum s v) herr horth
    (P.diagonal_lower_partial a s ha v)
  have hb := P.diagonal_partial_residual a s c v hK hcoeff hzero
  have hd : ‖A v - c • v‖ ≤ (1 + K) * δ * ‖v‖ := by
    calc
      ‖A v - c • v‖ ≤ ‖A v - P.diagonal a v‖ + ‖P.diagonal a v - c • v‖ := by
        simpa only [dist_eq_norm] using dist_triangle (A v) (P.diagonal a v) (c • v)
      _ ≤ δ * ‖v‖ + K * ‖P.blockSum s v‖ := add_le_add herr hb
      _ ≤ δ * ‖v‖ + K * (δ * ‖v‖) := add_le_add_right (mul_le_mul_of_nonneg_left hw hK) _
      _ = (1 + K) * δ * ‖v‖ := by ring
  calc
    ‖D (A v) - c • D v‖ = ‖D (A v - c • v)‖ := by rw [map_sub, map_smul]
    _ ≤ L * ‖A v - c • v‖ := hD _
    _ ≤ L * ((1 + K) * δ * ‖v‖) := mul_le_mul_of_nonneg_left hd hL
    _ ≤ L * ((1 + K) * δ * (R * ‖D v‖)) := by
      gcongr
    _ = L * (1 + K) * δ * R * ‖D v‖ := by ring

end OrthogonalBlocks
end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open scoped BigOperators
namespace HighOrderWalks.TwoSided.Fresh
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma flag_raising_estimate (F : ℕ → Submodule ℝ E) (hF : Monotone F)
    (r : ℕ) (htop : F r = ⊤) (D : E →ₗ[ℝ] H) (A : E →ₗ[ℝ] E)
    {e : ℝ} (he : 0 ≤ e) (hsmall : Real.sqrt ((r : ℝ) + 1) * e ≤ 1 / 2)
    (henergy : ∀ x, inner ℝ (A x) x = ‖D x‖ ^ 2)
    (hblock : ∀ i x, ‖A ((flagBlocks F hF r htop).part i x) -
      ((r : ℝ) + 1 - (i : ℝ)) • (flagBlocks F hF r htop).part i x‖ ≤
        e * ‖(flagBlocks F hF r htop).part i x‖)
    (j : Fin (r + 1)) {v : E} (hv : v ∈ F j.val)
    (horth : ∀ i : ℕ, i < j.val → ∀ w ∈ F i, inner ℝ (A v) w = 0) :
    ‖D (A v) - ((r : ℝ) + 1 - (j : ℝ)) • D v‖ ≤
      2 * ((r : ℝ) + 1) * ((r : ℝ) + 2) * Real.sqrt ((r : ℝ) + 1) * e * ‖D v‖ := by
  classical
  let P := flagBlocks F hF r htop
  let a : Fin (r + 1) → ℝ := fun i => (r : ℝ) + 1 - (i : ℝ)
  let δ := Real.sqrt ((r : ℝ) + 1) * e
  let s : Finset (Fin (r + 1)) := Finset.univ.filter (fun i => i.val < j.val)
  have ha : ∀ i, 1 ≤ a i ∧ a i ≤ (r : ℝ) + 1 := by
    intro i
    have hi : (i : ℝ) ≤ (r : ℝ) := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
    have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg i.val
    dsimp [a]
    constructor <;> linarith
  have herr : ∀ x, ‖A x - P.diagonal a x‖ ≤ δ * ‖x‖ := by
    intro x
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, δ] using
      P.diagonal_residual A a he hblock x
  have hmaps := P.map_energy_bounds D A a (by have := Nat.cast_nonneg (α := ℝ) r; linarith : (1 : ℝ) ≤ (r : ℝ) + 1)
    hsmall ha herr henergy
  have hcoeff : ∀ i ∈ s, |a i - a j| ≤ (r : ℝ) := by
    intro i hi
    have hij : i.val < j.val := (Finset.mem_filter.mp hi).2
    have hir : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij.le
    have hjr : (j : ℝ) ≤ (r : ℝ) := by exact_mod_cast (Nat.le_of_lt_succ j.isLt)
    have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg i.val
    dsimp [a]
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hzero : ∀ i, i ∉ s → (a i - a j) • P.part i v = 0 := by
    intro i hi
    have hji : j.val ≤ i.val := by simpa [s] using hi
    rcases eq_or_lt_of_le hji with hij | hij
    · have heq : i = j := Fin.ext hij.symm
      subst i
      simp
    · have hz := flagBlocks_zero_above F hF r htop i hv hij
      change P.part i v = 0 at hz
      rw [hz, smul_zero]
  have horth' : inner ℝ (A v) (P.blockSum s v) = 0 := by
    rw [P.partial_apply, inner_sum]
    apply Finset.sum_eq_zero
    intro i hi
    exact horth i.val (Finset.mem_filter.mp hi).2 (P.part i v) (flagBlocks_mem F hF r htop i v)
  have h := P.raise_from_flag D A a v s (a j)
    (mul_nonneg (Real.sqrt_nonneg _) he) (Nat.cast_nonneg r)
    (by positivity : (0 : ℝ) ≤ (r : ℝ) + 2) (by norm_num : (0 : ℝ) ≤ 2)
    (herr v) (fun i _ => (ha i).1) hcoeff hzero horth'
    (fun x => by simpa only [add_assoc, one_add_one_eq_two] using (hmaps x).2) (hmaps v).1
  dsimp [a, δ] at h
  convert h using 1
  ring

end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

lemma native_raised_piece {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hk : k + 2 ≤ n)
    {e : ℝ} (he : 0 ≤ e) (hsmall : Real.sqrt ((k : ℝ) + 1) * e ≤ 1 / 2)
    (hblock : ∀ i x, ‖nativeEnergy hX hm (show k + 1 ≤ n by omega)
      ((nativeFlagBlocks hm (show k ≤ n by omega)).part i x) -
      ((k : ℝ) + 1 - (i : ℝ)) • (nativeFlagBlocks hm (show k ≤ n by omega)).part i x‖ ≤
        e * ‖(nativeFlagBlocks hm (show k ≤ n by omega)).part i x‖)
    (j : Fin (k + 2)) (hj : j.val < k + 1)
    (u : meanZeroSpace X m (k + 2))
    (hu : u ∈ flagPiece (levelFlag X m (k + 1)) j.val) :
    ‖upZero hm (show k + 1 ≤ n by omega) (downZero hX hm u) -
      ((k : ℝ) + 1 - (j : ℝ)) • u‖ ≤
      2 * ((k : ℝ) + 1) * ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 1) * e * ‖u‖ := by
  let hkprev : k + 1 ≤ n := by omega
  have huF := flagPiece_le (levelFlag X m (k + 1)) j.val hu
  rw [levelFlag_succ hm hkprev (by omega : j.val ≤ k)] at huF
  obtain ⟨v, hv, huv⟩ := huF
  have ho : ∀ i : ℕ, i < j.val → ∀ w ∈ levelFlag X m k i,
      inner ℝ (nativeEnergy hX hm hkprev v) w = 0 := by
    intro i hij w hw
    have hj0 : j.val ≠ 0 := by omega
    obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    have huperp : u ∈ (levelFlag X m (k + 1) l)ᗮ := by
      rw [hl] at hu
      exact hu.2
    have hw' : upZero hm hkprev w ∈ levelFlag X m (k + 1) i := by
      rw [levelFlag_succ hm hkprev (by omega : i ≤ k)]
      exact ⟨w, hw, rfl⟩
    have hw'' : upZero hm hkprev w ∈ levelFlag X m (k + 1) l :=
      levelFlag_mono hm hkprev (by omega) hw'
    rw [nativeEnergy_inner, huv]
    exact Submodule.inner_left_of_mem_orthogonal hw'' huperp
  have hr := flag_raising_estimate (levelFlag X m k) (levelFlag_mono hm (by omega : k ≤ n))
    k (levelFlag_top hm k) (upZero hm hkprev) (nativeEnergy hX hm hkprev) he hsmall
    (nativeEnergy_energy hX hm hkprev) hblock (⟨j.val, hj⟩ : Fin (k + 1)) hv ho
  change ‖upZero hm hkprev (downZero hX hm (upZero hm hkprev v)) -
    ((k : ℝ) + 1 - (j : ℝ)) • upZero hm hkprev v‖ ≤ _ at hr
  rwa [huv] at hr

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem mem_link {X : Finset (Finset V)} {η τ : Finset V} :
    τ ∈ link X η ↔ τ ∈ X ∧ Disjoint η τ ∧ η ∪ τ ∈ X := by
  simp [link]

theorem link_union_injective (X : Finset (Finset V)) (η : Finset V) :
    Set.InjOn (fun τ => η ∪ τ) (↑(link X η) : Set (Finset V)) := by
  intro τ hτ σ hσ he
  change η ∪ τ = η ∪ σ at he
  have ht := (mem_link.mp hτ).2.1
  have hs := (mem_link.mp hσ).2.1
  apply Finset.ext
  intro v
  have hte : v ∈ τ → v ∉ η := fun hv hη => Finset.disjoint_left.mp ht hη hv
  have hse : v ∈ σ → v ∉ η := fun hv hη => Finset.disjoint_left.mp hs hη hv
  have hv : v ∈ η ∪ τ ↔ v ∈ η ∪ σ := by rw [he]
  simp only [Finset.mem_union] at hv
  tauto

theorem link_image_union {X : Finset (Finset V)} {n : ℕ}
    (hX : IsPureComplex X n) (η : Finset V) :
    (link X η).image (fun τ => η ∪ τ) = X.filter (fun σ => η ⊆ σ) := by
  ext σ
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨(mem_link.mp hτ).2.2, Finset.subset_union_left⟩
  · rintro ⟨hσ, hησ⟩
    refine ⟨σ \ η, ?_, Finset.union_sdiff_of_subset hησ⟩
    apply mem_link.mpr
    refine ⟨hX.1 σ hσ _ Finset.sdiff_subset, Finset.disjoint_sdiff, ?_⟩
    simpa only [Finset.union_sdiff_of_subset hησ] using hσ

theorem sum_link_union {X : Finset (Finset V)} {n : ℕ}
    (hX : IsPureComplex X n) (η : Finset V) (F : Finset V → ℝ) :
    (∑ τ ∈ link X η, F (η ∪ τ)) = ∑ σ ∈ X.filter (fun σ => η ⊆ σ), F σ := by
  rw [← link_image_union hX η, Finset.sum_image (link_union_injective X η)]

theorem link_union_card {X : Finset (Finset V)} {η τ : Finset V}
    (hτ : τ ∈ link X η) : (η ∪ τ).card = η.card + τ.card :=
  Finset.card_union_of_disjoint (mem_link.mp hτ).2.1

theorem link_subset_iff {X : Finset (Finset V)} {η τ σ : Finset V}
    (hτ : τ ∈ link X η) : η ∪ τ ⊆ η ∪ σ ↔ τ ⊆ σ := by
  constructor
  · intro h v hv
    have hmem := h (Finset.mem_union_right η hv)
    rcases Finset.mem_union.mp hmem with hη | hσ
    · exact False.elim (Finset.disjoint_left.mp (mem_link.mp hτ).2.1 hη hv)
    · exact hσ
  · exact fun h => Finset.union_subset_union_right h

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem link_cofaces_image {X : Finset (Finset V)} {n : ℕ}
    (hX : IsPureComplex X n) {η τ : Finset V} (hτ : τ ∈ link X η) :
    ((link X η).filter (fun σ => σ.card = τ.card + 1 ∧ τ ⊆ σ)).image
      (fun σ => η ∪ σ) =
    X.filter (fun σ => σ.card = (η ∪ τ).card + 1 ∧ η ∪ τ ⊆ σ) := by
  ext σ
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨ρ, ⟨hρ, hc, ht⟩, rfl⟩
    refine ⟨(mem_link.mp hρ).2.2, ?_, Finset.union_subset_union_right ht⟩
    rw [link_union_card hρ, link_union_card hτ, hc]
    omega
  · rintro ⟨hσ, hc, ht⟩
    have he : η ⊆ σ := Finset.subset_union_left.trans ht
    have hu : η ∪ (σ \ η) = σ := Finset.union_sdiff_of_subset he
    have hr : σ \ η ∈ link X η := by
      apply mem_link.mpr
      refine ⟨hX.1 σ hσ _ Finset.sdiff_subset, Finset.disjoint_sdiff, ?_⟩
      simpa only [hu] using hσ
    refine ⟨σ \ η, ⟨hr, ?_, ?_⟩, hu⟩
    · have hh := link_union_card hr
      rw [hu] at hh
      rw [link_union_card hτ] at hc
      omega
    · exact (link_subset_iff hτ).mp (hu.symm ▸ ht)

theorem link_isWeight {X : Finset (Finset V)} {n : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) {η : Finset V}
    (hη : η.card ≤ n) : IsWeight (link X η) (n - η.card) (linkWeight m η) := by
  constructor
  · intro τ hτ
    exact hm.1 _ (mem_link.mp hτ).2.2
  · intro τ hτ hc
    change m (η ∪ τ) = _
    rw [hm.2 _ (mem_link.mp hτ).2.2 (by rw [link_union_card hτ]; omega)]
    rw [← link_cofaces_image hX hτ]
    rw [Finset.sum_image]
    · rfl
    · intro a ha b hb he
      exact link_union_injective X η (Finset.mem_filter.mp ha).1
        (Finset.mem_filter.mp hb).1 he

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem link_cells_image {X : Finset (Finset V)} {n : ℕ}
    (hX : IsPureComplex X n) (η : Finset V) (c : ℕ) :
    (cells (link X η) c).image (fun τ => η ∪ τ) =
      (cells X (η.card + c)).filter (fun σ => η ⊆ σ) := by
  ext σ
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    have ht := mem_cells.mp hτ
    exact ⟨mem_cells.mpr ⟨(mem_link.mp ht.1).2.2,
      (link_union_card ht.1).trans (congrArg (η.card + ·) ht.2)⟩,
      Finset.subset_union_left⟩
  · rintro ⟨hσ, he⟩
    have hu : η ∪ (σ \ η) = σ := Finset.union_sdiff_of_subset he
    have hr : σ \ η ∈ link X η := by
      apply mem_link.mpr
      refine ⟨hX.1 σ (mem_cells.mp hσ).1 _ Finset.sdiff_subset,
        Finset.disjoint_sdiff, ?_⟩
      simpa only [hu] using (mem_cells.mp hσ).1
    refine ⟨σ \ η, mem_cells.mpr ⟨hr, ?_⟩, hu⟩
    have hh := link_union_card hr
    rw [hu, (mem_cells.mp hσ).2] at hh
    omega

theorem sum_link_cells {X : Finset (Finset V)} {n : ℕ}
    (hX : IsPureComplex X n) (η : Finset V) (c : ℕ) (F : Finset V → ℝ) :
    (∑ τ ∈ cells (link X η) c, F (η ∪ τ)) =
      ∑ σ ∈ cells X (η.card + c), if η ⊆ σ then F σ else 0 := by
  rw [← Finset.sum_filter, ← link_cells_image hX η c, Finset.sum_image]
  intro a ha b hb he
  exact link_union_injective X η (mem_cells.mp ha).1 (mem_cells.mp hb).1 he

theorem localization_ip_sum {X : Finset (Finset V)} {n : ℕ}
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (k : ℕ) (f g : Finset V → ℝ) :
    (∑ η ∈ cells X k, ip (link X η) (linkWeight m η) 1 (loc f η) (loc g η)) =
      (k + 1 : ℝ) * ip X m (k + 1) f g := by
  have he (η : Finset V) (hη : η ∈ cells X k) :
      ip (link X η) (linkWeight m η) 1 (loc f η) (loc g η) =
        ∑ σ ∈ cells X (k + 1), if η ⊆ σ then m σ * f σ * g σ else 0 := by
    unfold ip linkWeight loc
    rw [sum_link_cells hX η 1 (fun σ => m σ * f σ * g σ), (mem_cells.mp hη).2]
  calc
    _ = ∑ η ∈ cells X k, ∑ σ ∈ cells X (k + 1),
        if η ⊆ σ then m σ * f σ * g σ else 0 := Finset.sum_congr rfl he
    _ = ∑ σ ∈ cells X (k + 1), ∑ η ∈ cells X k,
        if η ⊆ σ then m σ * f σ * g σ else 0 := Finset.sum_comm
    _ = _ := by
      unfold ip
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      have hs := mem_cells.mp hσ
      have hf : (cells X k).filter (fun η => η ⊆ σ) =
          X.filter (fun η => η ⊆ σ ∧ η.card + 1 = σ.card) := by
        ext η
        simp [cells, hs.2]
        tauto
      rw [← Finset.sum_filter, Finset.sum_const, hf,
        immediate_subfaces_card X n hX σ hs.1 (Finset.card_pos.mp (by omega))]
      simp only [hs.2, Nat.cast_add, Nat.cast_one, nsmul_eq_mul]

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem link_union_cells_iff {X : Finset (Finset V)} {n : ℕ}
    (hX : IsPureComplex X n) {η s t : Finset V}
    (hs : s ∈ link X η) (ht : t ∈ link X η) (c : ℕ) :
    s ∪ t ∈ cells (link X η) c ↔ (η ∪ s) ∪ (η ∪ t) ∈ cells X (η.card + c) := by
  have hd : Disjoint η (s ∪ t) := Finset.disjoint_union_right.mpr
    ⟨(mem_link.mp hs).2.1, (mem_link.mp ht).2.1⟩
  have hu : η ∪ (s ∪ t) = (η ∪ s) ∪ (η ∪ t) := by
    ext v
    simp only [Finset.mem_union]
    tauto
  constructor
  · intro h
    have hh := mem_cells.mp h
    apply mem_cells.mpr
    refine ⟨hu ▸ (mem_link.mp hh.1).2.2, ?_⟩
    rw [← hu, Finset.card_union_of_disjoint hd, hh.2]
  · intro h
    have hh := mem_cells.mp h
    have hx : η ∪ (s ∪ t) ∈ X := hu.symm ▸ hh.1
    apply mem_cells.mpr
    refine ⟨mem_link.mpr ⟨hX.1 _ hx _ Finset.subset_union_right, hd, hx⟩, ?_⟩
    have hc := hh.2
    rw [← hu, Finset.card_union_of_disjoint hd] at hc
    omega

theorem link_union_ne_iff {X : Finset (Finset V)} {η s t : Finset V}
    (hs : s ∈ link X η) (ht : t ∈ link X η) :
    s ≠ t ↔ η ∪ s ≠ η ∪ t := by
  constructor
  · intro h he
    exact h (link_union_injective X η hs ht he)
  · intro h he
    exact h (congrArg (fun u => η ∪ u) he)

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem vertex_nonLazy {X : Finset (Finset V)} {m : Finset V → ℝ}
    {s : Finset V} (hs : s ∈ cells X 1) (f : Finset V → ℝ) :
    nonLazyWalk X m f s = ∑ t ∈ cells X 1,
      if t ≠ s ∧ s ∪ t ∈ cells X 2 then m (s ∪ t) / m s * f t else 0 := by
  have h := mem_cells.mp hs
  have he : X.filter (fun t => t.card = s.card ∧ t ≠ s ∧ s ∪ t ∈ X ∧
      (s ∪ t).card = s.card + 1) =
      (cells X 1).filter (fun t => t ≠ s ∧ s ∪ t ∈ cells X 2) := by
    ext t
    simp [cells, h.2, and_assoc]
  rw [nonLazyWalk, if_pos h.1, upperWalk, if_pos h.1, he]
  simp only [h.2, Nat.cast_one,
    div_one, one_add_one_eq_two, Finset.sum_filter]
  have hh : (2 : ℝ) * (∑ t ∈ cells X 1,
      if t ≠ s ∧ s ∪ t ∈ cells X 2 then m (s ∪ t) / (2 * m s) * f t else 0) =
      ∑ t ∈ cells X 1,
        if t ≠ s ∧ s ∪ t ∈ cells X 2 then m (s ∪ t) / m s * f t else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> ring
  linarith

theorem vertex_nonLazy_ip {X : Finset (Finset V)} {m : Finset V → ℝ}
    (hm : ∀ s ∈ cells X 1, m s ≠ 0) (f g : Finset V → ℝ) :
    ip X m 1 (nonLazyWalk X m f) g =
      ∑ s ∈ cells X 1, ∑ t ∈ cells X 1,
        if t ≠ s ∧ s ∪ t ∈ cells X 2 then m (s ∪ t) * f t * g s else 0 := by
  unfold ip
  apply Finset.sum_congr rfl
  intro s hs
  rw [vertex_nonLazy hs, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs
  · field_simp [hm s hs]
  · ring

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem sum_link_cells_pair {X : Finset (Finset V)} {n : ℕ}
    (hX : IsPureComplex X n) (η : Finset V) (F : Finset V → Finset V → ℝ) :
    (∑ s ∈ cells (link X η) 1, ∑ t ∈ cells (link X η) 1, F (η ∪ s) (η ∪ t)) =
      ∑ s ∈ cells X (η.card + 1), ∑ t ∈ cells X (η.card + 1),
        if η ⊆ s ∧ η ⊆ t then F s t else 0 := by
  have hi (s : Finset V) :
      (∑ t ∈ cells (link X η) 1, F (η ∪ s) (η ∪ t)) =
      ∑ t ∈ cells X (η.card + 1), if η ⊆ t then F (η ∪ s) t else 0 :=
    sum_link_cells hX η 1 (F (η ∪ s))
  simp_rw [hi]
  rw [sum_link_cells hX η 1 (fun s =>
    ∑ t ∈ cells X (η.card + 1), if η ⊆ t then F s t else 0)]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : η ⊆ s <;> simp [hs]

theorem link_nonLazy_ip_sum {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) {η : Finset V}
    (hη : η ∈ cells X k) (f g : Finset V → ℝ) :
    ip (link X η) (linkWeight m η) 1
      (nonLazyWalk (link X η) (linkWeight m η) (loc f η)) (loc g η) =
      ∑ s ∈ cells X (k + 1), ∑ t ∈ cells X (k + 1),
        if η ⊆ s ∧ η ⊆ t then
          (if t ≠ s ∧ s ∪ t ∈ cells X (k + 2) then m (s ∪ t) * f t * g s else 0)
        else 0 := by
  rw [vertex_nonLazy_ip (X := link X η) (m := linkWeight m η) (fun s hs =>
    (hm.1 _ (mem_link.mp (mem_cells.mp hs).1).2.2).ne') (loc f η) (loc g η)]
  have hh : (∑ s ∈ cells (link X η) 1, ∑ t ∈ cells (link X η) 1,
      if t ≠ s ∧ s ∪ t ∈ cells (link X η) 2 then
        linkWeight m η (s ∪ t) * loc f η t * loc g η s else 0) =
      ∑ s ∈ cells (link X η) 1, ∑ t ∈ cells (link X η) 1,
        if η ∪ t ≠ η ∪ s ∧ (η ∪ s) ∪ (η ∪ t) ∈ cells X (η.card + 2) then
          m ((η ∪ s) ∪ (η ∪ t)) * f (η ∪ t) * g (η ∪ s) else 0 := by
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro t ht
    simp only [link_union_ne_iff (mem_cells.mp ht).1 (mem_cells.mp hs).1,
      link_union_cells_iff hX (mem_cells.mp hs).1 (mem_cells.mp ht).1]
    have hu : η ∪ (s ∪ t) = (η ∪ s) ∪ (η ∪ t) := by
      ext v
      simp only [Finset.mem_union]
      tauto
    simp only [linkWeight, loc, hu]
  rw [hh, sum_link_cells_pair hX η (fun s t =>
    if t ≠ s ∧ s ∪ t ∈ cells X (η.card + 2) then m (s ∪ t) * f t * g s else 0),
    (mem_cells.mp hη).2]

end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh

lemma common_subface_sum {V : Type*} [DecidableEq V]
    (X : Finset (Finset V)) (k : ℕ) (s t : Finset V)
    (hs : s ∈ cells X (k + 1)) (ht : t ∈ cells X (k + 1))
    (hne : s ≠ t) (F : Finset V → ℝ) :
    (∑ η ∈ cells X k, if η ⊆ s ∧ η ⊆ t then F η else 0) =
      if s ∩ t ∈ cells X k then F (s ∩ t) else 0 := by
  have hsc := (mem_cells.mp hs).2
  have htc := (mem_cells.mp ht).2
  have heq (η : Finset V) (hη : η ∈ cells X k) (hsub : η ⊆ s ∧ η ⊆ t) :
      η = s ∩ t := by
    apply common_immediate_subface_eq_inter s t η hne (hsc.trans htc.symm) hsub.1 hsub.2
    have hc := (mem_cells.mp hη).2
    omega
  by_cases hm : s ∩ t ∈ cells X k
  · rw [if_pos hm]
    calc
      (∑ η ∈ cells X k, if η ⊆ s ∧ η ⊆ t then F η else 0) =
          (if s ∩ t ⊆ s ∧ s ∩ t ⊆ t then F (s ∩ t) else 0) := by
        apply Finset.sum_eq_single
        · intro η hη hneq
          split_ifs with hsub
          · exact False.elim (hneq (heq η hη hsub))
          · rfl
        · intro hnot
          exact False.elim (hnot hm)
      _ = F (s ∩ t) := if_pos ⟨Finset.inter_subset_left, Finset.inter_subset_right⟩
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro η hη
    split_ifs with hsub
    · have hh := heq η hη hsub
      exact False.elim (hm (hh ▸ hη))
    · rfl

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem global_link_edges {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (f g : Finset V → ℝ) :
    (∑ η ∈ cells X k, ip (link X η) (linkWeight m η) 1
      (nonLazyWalk (link X η) (linkWeight m η) (loc f η)) (loc g η)) =
      ∑ s ∈ cells X (k + 1), ∑ t ∈ cells X (k + 1),
        if t ≠ s ∧ s ∪ t ∈ cells X (k + 2) then m (s ∪ t) * f t * g s else 0 := by
  calc
    _ = ∑ η ∈ cells X k, ∑ s ∈ cells X (k + 1), ∑ t ∈ cells X (k + 1),
        if η ⊆ s ∧ η ⊆ t then
          (if t ≠ s ∧ s ∪ t ∈ cells X (k + 2) then m (s ∪ t) * f t * g s else 0)
        else 0 := Finset.sum_congr rfl (fun η hη => link_nonLazy_ip_sum hX hm hη f g)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      by_cases h : t ≠ s ∧ s ∪ t ∈ cells X (k + 2)
      · have hi : s ∩ t ∈ cells X k := by
          apply mem_cells.mpr
          refine ⟨hX.1 s (mem_cells.mp hs).1 _ Finset.inter_subset_left, ?_⟩
          have hh := Finset.card_union_add_card_inter s t
          have hsc := (mem_cells.mp hs).2
          have htc := (mem_cells.mp ht).2
          have huc := (mem_cells.mp h.2).2
          omega
        rw [common_subface_sum X k s t hs ht (Ne.symm h.1)]
        simp only [if_pos hi]
      · simp [h]

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem coface_kernel_offdiag {X : Finset (Finset V)} {m : Finset V → ℝ}
    {c : ℕ} {s t : Finset V} (hs : s ∈ cells X c) (ht : t ∈ cells X c)
    (hst : s ≠ t) :
    (∑ u ∈ cells X (c + 1), if s ⊆ u ∧ t ⊆ u then m u else 0) =
      if s ∪ t ∈ cells X (c + 1) then m (s ∪ t) else 0 := by
  have huniq (u : Finset V) (hu : u ∈ cells X (c + 1))
      (h : s ⊆ u ∧ t ⊆ u) : u = s ∪ t :=
    common_immediate_coface_eq_union s t u hst
      ((mem_cells.mp hs).2.trans (mem_cells.mp ht).2.symm) h.1 h.2
      (by rw [(mem_cells.mp hu).2, (mem_cells.mp hs).2])
  by_cases he : s ∪ t ∈ cells X (c + 1)
  · rw [if_pos he, Finset.sum_eq_single (s ∪ t)]
    · simp only [Finset.subset_union_left, Finset.subset_union_right, and_self, if_true]
    · intro u hu hne
      split_ifs with h
      · exact False.elim (hne (huniq u hu h))
      · rfl
    · exact fun h => False.elim (h he)
  · rw [if_neg he]
    apply Finset.sum_eq_zero
    intro u hu
    split_ifs with h
    · exact False.elim (he (huniq u hu h ▸ hu))
    · rfl

theorem coface_kernel_diag {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (hc : c ≤ n) {s : Finset V} (hs : s ∈ cells X c) :
    (∑ u ∈ cells X (c + 1), if s ⊆ u ∧ s ⊆ u then m u else 0) = m s := by
  have he : (cells X (c + 1)).filter (fun u => s ⊆ u) =
      X.filter (fun u => u.card = s.card + 1 ∧ s ⊆ u) := by
    ext u
    simp [cells, (mem_cells.mp hs).2]
    tauto
  simp only [and_self]
  rw [← Finset.sum_filter, he]
  exact (hm.2 s (mem_cells.mp hs).1 (by rw [(mem_cells.mp hs).2]; exact hc)).symm

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem dStar_dS_kernel {X : Finset (Finset V)} {m : Finset V → ℝ}
    {c : ℕ} {s : Finset V} (hs : s ∈ cells X c) (f : Finset V → ℝ) :
    dStar X m (dS X f) s =
      ∑ t ∈ cells X c, ((∑ u ∈ cells X (c + 1),
        if s ⊆ u ∧ t ⊆ u then m u else 0) / m s) * f t := by
  rw [dStar_cell hs]
  calc
    _ = ∑ u ∈ cells X (c + 1), ∑ t ∈ cells X c,
        if s ⊆ u ∧ t ⊆ u then m u / m s * f t else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [dS_cell hu]
      by_cases hsu : s ⊆ u
      · simp only [hsu, if_true, Finset.mul_sum, true_and]
        apply Finset.sum_congr rfl
        intro t _
        split_ifs <;> ring
      · simp [hsu]
    _ = ∑ t ∈ cells X c, ∑ u ∈ cells X (c + 1),
        if s ⊆ u ∧ t ⊆ u then m u / m s * f t else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.sum_div, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u _
      split_ifs <;> ring

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem dStar_dS_split {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (hc : c ≤ n) {s : Finset V} (hs : s ∈ cells X c)
    (f : Finset V → ℝ) :
    dStar X m (dS X f) s = f s + ∑ t ∈ cells X c,
      if t ≠ s ∧ s ∪ t ∈ cells X (c + 1) then m (s ∪ t) / m s * f t else 0 := by
  rw [dStar_dS_kernel hs]
  have hh : (∑ t ∈ cells X c, ((∑ u ∈ cells X (c + 1),
      if s ⊆ u ∧ t ⊆ u then m u else 0) / m s) * f t) =
      ∑ t ∈ cells X c, ((if t = s then f s else 0) +
        if t ≠ s ∧ s ∪ t ∈ cells X (c + 1) then m (s ∪ t) / m s * f t else 0) := by
    apply Finset.sum_congr rfl
    intro t ht
    by_cases he : t = s
    · subst t
      rw [coface_kernel_diag hm hc hs]
      simp [div_self (hm.1 s (mem_cells.mp hs).1).ne']
    · rw [coface_kernel_offdiag hs ht (Ne.symm he)]
      split_ifs <;> simp_all
  rw [hh, Finset.sum_add_distrib]
  simp [hs]

theorem upper_identity {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (hc : c ≤ n) {s : Finset V} (hs : s ∈ cells X c)
    (f : Finset V → ℝ) :
    dStar X m (dS X f) s = (c + 1 : ℝ) * upperWalk X m f s := by
  have h := mem_cells.mp hs
  have he : X.filter (fun t => t.card = s.card ∧ t ≠ s ∧ s ∪ t ∈ X ∧
      (s ∪ t).card = s.card + 1) =
      (cells X c).filter (fun t => t ≠ s ∧ s ∪ t ∈ cells X (c + 1)) := by
    ext t
    simp [cells, h.2, and_assoc]
  rw [dStar_dS_split hm hc hs, upperWalk, if_pos h.1, he, Finset.sum_filter,
    h.2, mul_add, Finset.mul_sum]
  congr 1
  · field_simp
  · apply Finset.sum_congr rfl
    intro t _
    split_ifs
    · field_simp
    · ring

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem upper_mean {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hc : c ≤ n)
    (f : Finset V → ℝ) :
    ip X m c (upperWalk X m f) (fun _ => 1) = ip X m c f (fun _ => 1) := by
  have hd := dStar_mean hX hm (c := c) (dS X f)
  rw [dS_mean hm hc f] at hd
  have he : ip X m c (dStar X m (dS X f)) (fun _ => 1) =
      (c + 1 : ℝ) * ip X m c (upperWalk X m f) (fun _ => 1) := by
    unfold ip
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [upper_identity hm hc hs]
    ring
  rw [he] at hd
  exact (mul_left_cancel₀ (by positivity : (c + 1 : ℝ) ≠ 0)) hd

theorem nonLazy_mean {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hc : c ≤ n) (hc0 : 0 < c)
    (f : Finset V → ℝ) :
    ip X m c (nonLazyWalk X m f) (fun _ => 1) = ip X m c f (fun _ => 1) := by
  have he : ip X m c (nonLazyWalk X m f) (fun _ => 1) =
      ((c + 1 : ℝ) / c) * ip X m c (upperWalk X m f) (fun _ => 1) -
        ip X m c f (fun _ => 1) / c := by
    unfold ip
    rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    have h := mem_cells.mp hs
    simp only [nonLazyWalk, if_pos h.1, h.2]
    ring
  rw [he, upper_mean hX hm hc]
  have hcne : (c : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hc0)
  field_simp [hcne]
  ring

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem dStar_congr_cell {X : Finset (Finset V)} {m : Finset V → ℝ} {c : ℕ}
    {s : Finset V} (hs : s ∈ cells X c) {f g : Finset V → ℝ}
    (he : ∀ t ∈ cells X (c + 1), f t = g t) : dStar X m f s = dStar X m g s := by
  rw [dStar_cell hs, dStar_cell hs]
  apply Finset.sum_congr rfl
  intro t ht
  rw [he t ht]

theorem upper_one_cell {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hc : c ≤ n)
    {s : Finset V} (hs : s ∈ cells X c) : upperWalk X m (fun _ => 1) s = 1 := by
  have hh := upper_identity hm hc hs (fun _ => 1)
  have he : dStar X m (dS X (fun _ => 1)) s = (c + 1 : ℝ) := by
    rw [dStar_congr_cell hs (fun t ht => dS_one_cell hX ht)]
    have hlin := congrFun ((dStarLinear X m).map_smul (c + 1 : ℝ) (fun _ => 1)) s
    change dStar X m (fun _ => (c + 1 : ℝ) * 1) s =
      (c + 1 : ℝ) * dStar X m (fun _ => 1) s at hlin
    simpa only [mul_one, dStar_one_cell hm hc hs] using hlin
  rw [he] at hh
  nlinarith

theorem nonLazy_one_cell {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hc : c ≤ n) (hc0 : 0 < c)
    {s : Finset V} (hs : s ∈ cells X c) : nonLazyWalk X m (fun _ => 1) s = 1 := by
  have h := mem_cells.mp hs
  simp only [nonLazyWalk, if_pos h.1, h.2, upper_one_cell hX hm hc hs, mul_one]
  have hcne : (c : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hc0)
  field_simp [hcne]
  ring

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

def upperLinear (X : Finset (Finset V)) (m : Finset V → ℝ) :
    (Finset V → ℝ) →ₗ[ℝ] (Finset V → ℝ) where
  toFun := upperWalk X m
  map_add' f g := by
    funext s
    by_cases hs : s ∈ X <;> simp [upperWalk, hs, add_div, mul_add,
      Finset.sum_add_distrib]
    ring
  map_smul' a f := by
    funext s
    by_cases hs : s ∈ X <;> simp [upperWalk, hs, Finset.mul_sum, mul_add,
      mul_div_assoc, mul_left_comm]

def nonLazyLinear (X : Finset (Finset V)) (m : Finset V → ℝ) :
    (Finset V → ℝ) →ₗ[ℝ] (Finset V → ℝ) where
  toFun := nonLazyWalk X m
  map_add' f g := by
    funext s
    have hh := congrFun ((upperLinear X m).map_add f g) s
    change upperWalk X m (f + g) s = upperWalk X m f s + upperWalk X m g s at hh
    by_cases hs : s ∈ X <;> simp [nonLazyWalk, hs, hh, add_div, mul_add]
    ring
  map_smul' a f := by
    funext s
    have hh := congrFun ((upperLinear X m).map_smul a f) s
    change upperWalk X m (a • f) s = a * upperWalk X m f s at hh
    by_cases hs : s ∈ X <;> simp [nonLazyWalk, hs, hh]
    ring

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem dS_congr_cell {X : Finset (Finset V)} {c : ℕ} {s : Finset V}
    (hs : s ∈ cells X (c + 1)) {f g : Finset V → ℝ}
    (he : ∀ t ∈ cells X c, f t = g t) : dS X f s = dS X g s := by
  rw [dS_cell hs, dS_cell hs]
  apply Finset.sum_congr rfl
  intro t ht
  rw [he t ht]

theorem upper_congr_cell {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (hc : c ≤ n) {s : Finset V} (hs : s ∈ cells X c)
    {f g : Finset V → ℝ} (he : ∀ t ∈ cells X c, f t = g t) :
    upperWalk X m f s = upperWalk X m g s := by
  have hh := dStar_congr_cell (m := m) hs (fun t ht => dS_congr_cell ht he)
  rw [upper_identity hm hc hs, upper_identity hm hc hs] at hh
  exact (mul_left_cancel₀ (by positivity : (c + 1 : ℝ) ≠ 0)) hh

theorem nonLazy_congr_cell {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (hc : c ≤ n) {s : Finset V} (hs : s ∈ cells X c)
    {f g : Finset V → ℝ} (he : ∀ t ∈ cells X c, f t = g t) :
    nonLazyWalk X m f s = nonLazyWalk X m g s := by
  simp only [nonLazyWalk, if_pos (mem_cells.mp hs).1,
    upper_congr_cell hm hc hs he, he s hs]

end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh

lemma vertex_lowerWalk_mean {V : Type*} [DecidableEq V]
    (X : Finset (Finset V)) (m f : Finset V → ℝ)
    (τ : Finset V) (hτ : τ ∈ cells X 1) (hempty : (∅ : Finset V) ∈ X) :
    lowerWalk X m f τ = (∑ σ ∈ cells X 1, m σ * f σ) / m ∅ := by
  have hτX := (mem_cells.mp hτ).1
  have hcard := (mem_cells.mp hτ).2
  have hdiag : X.filter (fun η => η ⊆ τ ∧ η.card + 1 = τ.card) = {∅} := by
    ext η
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, _, hc⟩
      exact Finset.card_eq_zero.mp (by omega)
    · rintro rfl
      exact ⟨hempty, Finset.empty_subset _, by simp [hcard]⟩
  have hinter (σ : Finset V) (hc : σ.card = 1) (hne : σ ≠ τ) : τ ∩ σ = ∅ := by
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hcard
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc
    subst τ
    subst σ
    have huv : u ≠ v := by intro h; subst v; exact hne rfl
    simp [huv]
  have hoff : X.filter (fun σ => σ.card = τ.card ∧ σ ≠ τ ∧ τ ∩ σ ∈ X ∧
      (τ ∩ σ).card + 1 = τ.card) = (cells X 1).erase τ := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hσX, hc, hne, _, _⟩
      exact ⟨hne, mem_cells.mpr ⟨hσX, hc.trans hcard⟩⟩
    · rintro ⟨hne, hσ⟩
      have hc := (mem_cells.mp hσ).2
      have hi := hinter σ hc hne
      exact ⟨(mem_cells.mp hσ).1, hc.trans hcard.symm, hne,
        by simpa [hi] using hempty, by simp [hi, hcard]⟩
  unfold lowerWalk
  rw [if_pos hτX, hdiag, hoff]
  simp only [Finset.sum_singleton, hcard, Nat.cast_one, one_mul]
  have hsum : (∑ σ ∈ (cells X 1).erase τ, m σ / m (τ ∩ σ) * f σ) =
      (∑ σ ∈ (cells X 1).erase τ, m σ * f σ) / m ∅ := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro σ hσ
    have hm := Finset.mem_erase.mp hσ
    rw [hinter σ (mem_cells.mp hm.2).2 hm.1]
    ring
  rw [hsum]
  have hs := Finset.add_sum_erase (cells X 1) (fun σ => m σ * f σ) hτ
  rw [← hs]
  ring

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open scoped BigOperators
namespace HighOrderWalks.TwoSided.Fresh

theorem weighted_center_zero {ι : Type*} (s : Finset ι) (w f : ι → ℝ) (a : ℝ)
    (ha : a * ∑ i ∈ s, w i = ∑ i ∈ s, w i * f i) :
    (∑ i ∈ s, w i * (f i - a)) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  nlinarith [ha]

theorem weighted_center_square {ι : Type*} (s : Finset ι) (w f : ι → ℝ) (a : ℝ)
    (ha : a * ∑ i ∈ s, w i = ∑ i ∈ s, w i * f i) :
    (∑ i ∈ s, w i * (f i - a) ^ 2) =
      (∑ i ∈ s, w i * f i ^ 2) - a ^ 2 * ∑ i ∈ s, w i := by
  have he : (∑ i ∈ s, w i * (f i - a) ^ 2) =
      (∑ i ∈ s, w i * f i ^ 2) - 2 * a * (∑ i ∈ s, w i * f i) +
        a ^ 2 * (∑ i ∈ s, w i) := by
    calc
      _ = ∑ i ∈ s, (w i * f i ^ 2 - (2*a) * (w i*f i) + a^2*w i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
  rw [he, ← ha]
  ring

theorem weighted_center_contract {ι : Type*} (s : Finset ι) (w f : ι → ℝ) (a : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (ha : a * ∑ i ∈ s, w i = ∑ i ∈ s, w i * f i) :
    (∑ i ∈ s, w i * (f i - a) ^ 2) ≤ ∑ i ∈ s, w i * f i ^ 2 := by
  rw [weighted_center_square s w f a ha]
  exact sub_le_self _ (mul_nonneg (sq_nonneg a) (Finset.sum_nonneg hw))

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem vertex_mass {X : Finset (Finset V)} {n : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (he : (∅ : Finset V) ∈ X) :
    ∑ σ ∈ cells X 1, m σ = m ∅ := by
  have h := hm.2 ∅ he (by simp)
  simpa only [Finset.card_empty, zero_add, Finset.empty_subset, and_true, cells] using h.symm

theorem vertex_center_mean {X : Finset (Finset V)} {n : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (he : (∅ : Finset V) ∈ X) (f : Finset V → ℝ) :
    ip X m 1 (fun σ => f σ - lowerWalk X m f σ) (fun _ => 1) = 0 := by
  have ha : ((∑ σ ∈ cells X 1, m σ * f σ) / m ∅) *
      ∑ σ ∈ cells X 1, m σ = ∑ σ ∈ cells X 1, m σ * f σ := by
    rw [vertex_mass hm he]
    exact div_mul_cancel₀ _ (hm.1 ∅ he).ne'
  unfold ip
  simp only [mul_one]
  have hh := weighted_center_zero (cells X 1) m f _ ha
  convert hh using 1
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [vertex_lowerWalk_mean X m f σ hσ he]

theorem vertex_center_contract {X : Finset (Finset V)} {n : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (he : (∅ : Finset V) ∈ X) (f : Finset V → ℝ) :
    ip X m 1 (fun σ => f σ - lowerWalk X m f σ)
      (fun σ => f σ - lowerWalk X m f σ) ≤ ip X m 1 f f := by
  have ha : ((∑ σ ∈ cells X 1, m σ * f σ) / m ∅) *
      ∑ σ ∈ cells X 1, m σ = ∑ σ ∈ cells X 1, m σ * f σ := by
    rw [vertex_mass hm he]
    exact div_mul_cancel₀ _ (hm.1 ∅ he).ne'
  have hh := weighted_center_contract (cells X 1) m f _
    (fun σ hσ => (hm.1 σ (mem_cells.mp hσ).1).le) ha
  convert hh using 1
  · unfold ip
    apply Finset.sum_congr rfl
    intro σ hσ
    dsimp only
    rw [vertex_lowerWalk_mean X m f σ hσ he]
    ring
  · unfold ip
    apply Finset.sum_congr rfl
    intro σ _
    ring

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem centered_nonLazy_cell {X : Finset (Finset V)} {n : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hn : 1 ≤ n)
    (he : (∅ : Finset V) ∈ X) (f : Finset V → ℝ) {s : Finset V}
    (hs : s ∈ cells X 1) :
    nonLazyWalk X m (fun t => f t - lowerWalk X m f t) s = nonLazyWalk X m f s -
      (∑ t ∈ cells X 1, m t * f t) / m ∅ := by
  let a := (∑ t ∈ cells X 1, m t * f t) / m ∅
  have hcon : nonLazyWalk X m (fun t => f t - lowerWalk X m f t) s =
      nonLazyWalk X m (f - a • (fun _ => 1)) s := by
    apply nonLazy_congr_cell hm hn hs
    intro t ht
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one,
      vertex_lowerWalk_mean X m f t ht he]
    rfl
  rw [hcon]
  have hh := congrFun ((nonLazyLinear X m).map_sub f (a • (fun _ => 1))) s
  have hh' := congrFun ((nonLazyLinear X m).map_smul a (fun _ => 1)) s
  change nonLazyWalk X m (f - a • (fun _ => 1)) s =
    nonLazyWalk X m f s - nonLazyWalk X m (a • (fun _ => 1)) s at hh
  change nonLazyWalk X m (a • (fun _ => 1)) s = a * nonLazyWalk X m (fun _ => 1) s at hh'
  rw [hh, hh', nonLazy_one_cell hX hm hn (by omega) hs, mul_one]

theorem centered_nonLazy_ip {X : Finset (Finset V)} {n : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hn : 1 ≤ n)
    (he : (∅ : Finset V) ∈ X) (f g : Finset V → ℝ) :
    ip X m 1 (nonLazyWalk X m (fun t => f t - lowerWalk X m f t)) g =
      ip X m 1 (nonLazyWalk X m f) g -
        ((∑ t ∈ cells X 1, m t * f t) * (∑ t ∈ cells X 1, m t * g t)) / m ∅ := by
  unfold ip
  rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  rw [centered_nonLazy_cell hX hm hn he f hs]
  ring

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem link_vertex_sum {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) {η : Finset V}
    (hη : η ∈ cells X k) (f : Finset V → ℝ) :
    (∑ τ ∈ cells (link X η) 1, linkWeight m η τ * loc f η τ) =
      m η * dStar X m f η := by
  change (∑ τ ∈ cells (link X η) 1, m (η ∪ τ) * f (η ∪ τ)) = _
  rw [sum_link_cells hX η 1 (fun σ => m σ * f σ), (mem_cells.mp hη).2,
    dStar_cell hη, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs
  · field_simp [(hm.1 η (mem_cells.mp hη).1).ne']
  · ring

theorem link_vertex_product_sum {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (f g : Finset V → ℝ) :
    (∑ η ∈ cells X k,
      ((∑ τ ∈ cells (link X η) 1, linkWeight m η τ * loc f η τ) *
        (∑ τ ∈ cells (link X η) 1, linkWeight m η τ * loc g η τ)) /
          linkWeight m η ∅) = ip X m k (dStar X m f) (dStar X m g) := by
  unfold ip
  apply Finset.sum_congr rfl
  intro η hη
  rw [link_vertex_sum hX hm hη f, link_vertex_sum hX hm hη g]
  simp only [linkWeight, Finset.union_empty]
  field_simp [(hm.1 η (mem_cells.mp hη).1).ne']

end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh

lemma link_isPure {V : Type*} [DecidableEq V] {X : Finset (Finset V)} {n : ℕ}
    (hX : IsPureComplex X n) (η : Finset V) (hη : η ∈ X) (hc : η.card ≤ n) :
    IsPureComplex (link X η) (n - η.card) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ hσ τ hτσ
    have hs := mem_link.mp hσ
    apply mem_link.mpr
    refine ⟨hX.1 σ hs.1 τ hτσ, ?_, ?_⟩
    · exact hs.2.1.mono_right hτσ
    · exact hX.1 (η ∪ σ) hs.2.2 (η ∪ τ) (Finset.union_subset_union_right hτσ)
  · intro σ hσ
    have hbound := hX.2.1 (η ∪ σ) (mem_link.mp hσ).2.2
    have hsum := link_union_card hσ
    omega
  · intro σ hσ
    have hs := mem_link.mp hσ
    obtain ⟨ρ, hρ, hsub, hcard⟩ := hX.2.2.1 (η ∪ σ) hs.2.2
    have hηρ : η ⊆ ρ := fun _ hv => hsub (Finset.mem_union_left σ hv)
    have hσρ : σ ⊆ ρ := fun _ hv => hsub (Finset.mem_union_right η hv)
    refine ⟨ρ \ η, ?_, ?_, ?_⟩
    · apply mem_link.mpr
      refine ⟨hX.1 ρ hρ _ Finset.sdiff_subset, Finset.disjoint_sdiff, ?_⟩
      simpa only [Finset.union_sdiff_of_subset hηρ] using hρ
    · intro v hv
      apply Finset.mem_sdiff.mpr
      exact ⟨hσρ hv, fun hvη => Finset.disjoint_left.mp hs.2.1 hvη hv⟩
    · rw [Finset.card_sdiff_of_subset hηρ, hcard]
      omega
  · refine ⟨∅, mem_link.mpr ?_⟩
    refine ⟨hX.1 η hη ∅ (Finset.empty_subset _), ?_, ?_⟩
    · simp
    · simpa using hη

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem incidence_energy_split {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (hc : c ≤ n) (f g : Finset V → ℝ) :
    ip X m (c + 1) (dS X f) (dS X g) = ip X m c f g +
      ∑ s ∈ cells X c, ∑ t ∈ cells X c,
        if t ≠ s ∧ s ∪ t ∈ cells X (c + 1) then m (s ∪ t) * f t * g s else 0 := by
  rw [ip_symm, incidence_adjoint X m c
    (fun s hs => (hm.1 s (mem_cells.mp hs).1).ne')]
  unfold ip
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  rw [dStar_dS_split hm hc hs, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro t _
    split_ifs
    · field_simp [(hm.1 s (mem_cells.mp hs).1).ne']
    · ring

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem localization_identity {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hk : k + 1 ≤ n)
    (f g : Finset V → ℝ) :
    ip X m (k + 2) (dS X f) (dS X g) =
      ip X m k (dStar X m f) (dStar X m g) + ip X m (k + 1) f g +
        linkTerm X m k f g := by
  have he : linkTerm X m k f g =
      (∑ η ∈ cells X k, ip (link X η) (linkWeight m η) 1
        (nonLazyWalk (link X η) (linkWeight m η) (loc f η)) (loc g η)) -
      (∑ η ∈ cells X k,
        ((∑ τ ∈ cells (link X η) 1, linkWeight m η τ * loc f η τ) *
          (∑ τ ∈ cells (link X η) 1, linkWeight m η τ * loc g η τ)) /
            linkWeight m η ∅) := by
    unfold linkTerm
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro η hη
    have hc : η.card ≤ n := by rw [(mem_cells.mp hη).2]; omega
    have hlp := link_isPure hX η (mem_cells.mp hη).1 hc
    have hlw := link_isWeight hX hm hc
    have hempty : (∅ : Finset V) ∈ link X η := by
      apply mem_link.mpr
      exact ⟨hX.1 η (mem_cells.mp hη).1 _ (Finset.empty_subset _), by simp,
        by simpa using (mem_cells.mp hη).1⟩
    exact centered_nonLazy_ip hlp hlw (by rw [(mem_cells.mp hη).2]; omega)
      hempty (loc f η) (loc g η)
  rw [he, global_link_edges hX hm f g, link_vertex_product_sum hX hm f g,
    incidence_energy_split hm hk f g]
  ring

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem vertex_center_pair {X : Finset (Finset V)} {m : Finset V → ℝ}
    (he : (∅ : Finset V) ∈ X) (f g : Finset V → ℝ)
    (hg : ip X m 1 g (fun _ => 1) = 0) :
    ip X m 1 g f = ip X m 1 g (fun σ => f σ - lowerWalk X m f σ) := by
  have hz : (∑ σ ∈ cells X 1, m σ * g σ) = 0 := by
    simpa only [ip, mul_one] using hg
  have hh : ip X m 1 g (fun σ => f σ - lowerWalk X m f σ) =
      ip X m 1 g f - (∑ σ ∈ cells X 1, m σ * g σ) *
        ((∑ σ ∈ cells X 1, m σ * f σ) / m ∅) := by
    unfold ip
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro σ hσ
    dsimp only
    rw [vertex_lowerWalk_mean X m f σ hσ he]
    ring
  rw [hh, hz, zero_mul, sub_zero]

theorem linkSummand_bound {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    {lam : ℝ} (hX : IsPureComplex X n) (hm : IsWeight X n m)
    (hlam : 0 ≤ lam) (hk : k + 1 ≤ n) (hL : LinkTwoSided X m k lam)
    {η : Finset V} (hη : η ∈ cells X k) (f : Finset V → ℝ) :
    |linkSummand X m η f f| ≤ lam * ip (link X η) (linkWeight m η) 1 (loc f η) (loc f η) := by
  have hc : η.card ≤ n := by rw [(mem_cells.mp hη).2]; omega
  have hlp := link_isPure hX η (mem_cells.mp hη).1 hc
  have hlw := link_isWeight hX hm hc
  have he : (∅ : Finset V) ∈ link X η := by
    apply mem_link.mpr
    exact ⟨hX.1 η (mem_cells.mp hη).1 _ (Finset.empty_subset _), by simp,
      by simpa using (mem_cells.mp hη).1⟩
  let g := fun σ => loc f η σ - lowerWalk (link X η) (linkWeight m η) (loc f η) σ
  have hg : ip (link X η) (linkWeight m η) 1 g (fun _ => 1) = 0 :=
    vertex_center_mean hlw he (loc f η)
  have hmg : ip (link X η) (linkWeight m η) 1
      (nonLazyWalk (link X η) (linkWeight m η) g) (fun _ => 1) = 0 := by
    rw [nonLazy_mean hlp hlw (by rw [(mem_cells.mp hη).2]; omega) (by omega), hg]
  unfold linkSummand
  change |ip (link X η) (linkWeight m η) 1
    (nonLazyWalk (link X η) (linkWeight m η) g) (loc f η)| ≤ _
  rw [vertex_center_pair he (loc f η) _ hmg]
  exact (hL η hη g hg).trans (mul_le_mul_of_nonneg_left
    (vertex_center_contract hlw he (loc f η)) hlam)

theorem linkTerm_bound {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    {lam : ℝ} (hX : IsPureComplex X n) (hm : IsWeight X n m)
    (hlam : 0 ≤ lam) (hk : k + 1 ≤ n) (hL : LinkTwoSided X m k lam)
    (f : Finset V → ℝ) :
    |linkTerm X m k f f| ≤ (k + 1 : ℝ) * lam * ip X m (k + 1) f f := by
  unfold linkTerm
  calc
    _ ≤ ∑ η ∈ cells X k, |linkSummand X m η f f| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ η ∈ cells X k, lam * ip (link X η) (linkWeight m η) 1 (loc f η) (loc f η) :=
      Finset.sum_le_sum (fun η hη => linkSummand_bound hX hm hlam hk hL hη f)
    _ = _ := by
      rw [← Finset.mul_sum, localization_ip_sum hX m k f f]
      ring

end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
namespace HighOrderWalks.TwoSided.Fresh
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma symmetric_unit_inner_bound (A : E →ₗ[ℝ] E)
    (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y)) {C : ℝ}
    (hquad : ∀ x, |inner ℝ (A x) x| ≤ C * ‖x‖ ^ 2)
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    |inner ℝ (A u) v| ≤ C := by
  have hid : inner ℝ (A (u + v)) (u + v) - inner ℝ (A (u - v)) (u - v) =
      4 * inner ℝ (A u) v := by
    simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
    rw [hA v u, real_inner_comm v (A u)]
    ring
  have hh := (abs_sub_le (inner ℝ (A (u + v)) (u + v)) 0
    (inner ℝ (A (u - v)) (u - v))).trans (by
      simpa only [sub_zero, zero_sub, abs_neg] using add_le_add (hquad (u + v)) (hquad (u - v)))
  rw [hid, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hh
  rw [norm_add_sq_real, norm_sub_sq_real, hu, hv] at hh
  nlinarith

lemma symmetric_bilinear_bound (A : E →ₗ[ℝ] E)
    (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y)) {C : ℝ}
    (hquad : ∀ x, |inner ℝ (A x) x| ≤ C * ‖x‖ ^ 2) (x y : E) :
    |inner ℝ (A x) y| ≤ C * ‖x‖ * ‖y‖ := by
  by_cases hx : x = 0
  · subst x; simp
  by_cases hy : y = 0
  · subst y; simp
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hyn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  let u := ‖x‖⁻¹ • x
  let v := ‖y‖⁻¹ • y
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, hxn]
  have hv : ‖v‖ = 1 := by simp [v, norm_smul, hyn]
  have h := symmetric_unit_inner_bound A hA hquad u v hu hv
  have hid : |inner ℝ (A x) y| = ‖x‖ * ‖y‖ * |inner ℝ (A u) v| := by
    simp only [u, v, map_smul, real_inner_smul_left, real_inner_smul_right, abs_mul,
      abs_inv, abs_of_nonneg (norm_nonneg x), abs_of_nonneg (norm_nonneg y)]
    field_simp
  rw [hid]
  calc
    ‖x‖ * ‖y‖ * |inner ℝ (A u) v| ≤ ‖x‖ * ‖y‖ * C :=
      mul_le_mul_of_nonneg_left h (mul_nonneg (norm_nonneg x) (norm_nonneg y))
    _ = C * ‖x‖ * ‖y‖ := by ring

lemma symmetric_norm_bound (A : E →ₗ[ℝ] E)
    (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y)) {C : ℝ} (hC : 0 ≤ C)
    (hquad : ∀ x, |inner ℝ (A x) x| ≤ C * ‖x‖ ^ 2) (x : E) :
    ‖A x‖ ≤ C * ‖x‖ := by
  have h := symmetric_bilinear_bound A hA hquad x (A x)
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at h
  nlinarith [norm_nonneg (A x), mul_nonneg hC (norm_nonneg x)]

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

def nativeError {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hk : k + 1 ≤ n) :
    meanZeroSpace X m (k + 1) →ₗ[ℝ] meanZeroSpace X m (k + 1) :=
  (downZero hX hm (c := k + 1)).comp (upZero hm hk) -
    (upZero hm (show k ≤ n by omega)).comp (downZero hX hm (c := k)) - LinearMap.id

theorem nativeError_form {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hk : k + 1 ≤ n)
    (v w : meanZeroSpace X m (k + 1)) :
    inner ℝ (nativeError hX hm hk v) w =
      inner ℝ (upZero hm hk v) (upZero hm hk w) -
        inner ℝ (downZero hX hm v) (downZero hX hm w) - inner ℝ v w := by
  change inner ℝ (downZero hX hm (upZero hm hk v) -
    upZero hm (show k ≤ n by omega) (downZero hX hm v) - v) w = _
  rw [inner_sub_left, inner_sub_left,
    upZero_downZero_inner hX hm (show k ≤ n by omega)]
  have hh := nativeEnergy_inner hX hm hk v w
  change inner ℝ (downZero hX hm (upZero hm hk v)) w = _ at hh
  rw [hh]

theorem nativeError_symmetric {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hk : k + 1 ≤ n)
    (v w : meanZeroSpace X m (k + 1)) :
    inner ℝ (nativeError hX hm hk v) w = inner ℝ v (nativeError hX hm hk w) := by
  rw [← real_inner_comm v (nativeError hX hm hk w), nativeError_form, nativeError_form]
  have h1 := real_inner_comm (upZero hm hk v) (upZero hm hk w)
  have h2 := real_inner_comm (downZero hX hm (c := k) v) (downZero hX hm w)
  have h3 := real_inner_comm v w
  linarith

theorem nativeError_link {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hk : k + 1 ≤ n)
    (v w : meanZeroSpace X m (k + 1)) :
    inner ℝ (nativeError hX hm hk v) w =
      linkTerm X m k (decode X m (k + 1) v) (decode X m (k + 1) w) := by
  rw [nativeError_form]
  have he (a b : meanZeroSpace X m (k + 1)) :
      inner ℝ a b = ip X m (k + 1) (decode X m (k + 1) a) (decode X m (k + 1) b) := by
    rw [← encode_inner X m (k + 1) (fun σ hσ => (hm.1 σ (mem_cells.mp hσ).1).le),
      encode_decode X m (k + 1) (fun σ hσ => hm.1 σ (mem_cells.mp hσ).1),
      encode_decode X m (k + 1) (fun σ hσ => hm.1 σ (mem_cells.mp hσ).1)]
    rfl
  change inner ℝ (encode X m (k + 2) (dS X (decode X m (k + 1) v)))
      (encode X m (k + 2) (dS X (decode X m (k + 1) w))) -
    inner ℝ (encode X m k (dStar X m (decode X m (k + 1) v)))
      (encode X m k (dStar X m (decode X m (k + 1) w))) - inner ℝ v w = _
  rw [encode_inner X m (k + 2) (fun σ hσ => (hm.1 σ (mem_cells.mp hσ).1).le),
    encode_inner X m k (fun σ hσ => (hm.1 σ (mem_cells.mp hσ).1).le), he,
    localization_identity hX hm hk]
  ring

theorem nativeError_bound {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    {lam : ℝ} (hX : IsPureComplex X n) (hm : IsWeight X n m) (hk : k + 1 ≤ n)
    (hlam : 0 ≤ lam) (hL : LinkTwoSided X m k lam)
    (v : meanZeroSpace X m (k + 1)) :
    ‖nativeError hX hm hk v‖ ≤ ((k + 1 : ℝ) * lam) * ‖v‖ := by
  apply symmetric_norm_bound _ (nativeError_symmetric hX hm hk) (by positivity) _ v
  intro w
  rw [nativeError_link]
  have hh := linkTerm_bound hX hm hlam hk hL (decode X m (k + 1) w)
  have he : ip X m (k + 1) (decode X m (k + 1) w) (decode X m (k + 1) w) = ‖w‖ ^ 2 := by
    rw [← encode_inner X m (k + 1) (fun σ hσ => (hm.1 σ (mem_cells.mp hσ).1).le),
      encode_decode X m (k + 1) (fun σ hσ => hm.1 σ (mem_cells.mp hσ).1),
      real_inner_self_eq_norm_sq]
    rfl
  simpa only [he] using hh

end HighOrderWalks.TwoSided.Fresh
end

section
noncomputable section
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem meanZero_zero_level {X : Finset (Finset V)} {n : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (v : meanZeroSpace X m 0) : v = 0 := by
  obtain ⟨σ, hσ⟩ := hX.2.2.2
  have he : (∅ : Finset V) ∈ X := hX.1 σ hσ _ (Finset.empty_subset _)
  have hc : cells X 0 = {∅} := by
    ext τ
    simp only [mem_cells, Finset.card_eq_zero, Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · intro h
      subst τ
      exact ⟨he, rfl⟩
  have hz := decode_mean_zero (fun τ hτ => hm.1 τ (mem_cells.mp hτ).1) v
  simp only [ip, hc, Finset.sum_singleton, mul_one] at hz
  have hf : decode X m 0 v ∅ = 0 := (mul_eq_zero.mp hz).resolve_left (hm.1 ∅ he).ne'
  apply Subtype.ext
  rw [← encode_decode X m 0 (fun τ hτ => hm.1 τ (mem_cells.mp hτ).1) v]
  ext τ
  have ht : (τ : Finset V) = ∅ := Finset.card_eq_zero.mp (mem_cells.mp τ.2).2
  simp [encode, ht, hf]

theorem native_base_bound {X : Finset (Finset V)} {n : ℕ} {m : Finset V → ℝ}
    {lam : ℝ} (hX : IsPureComplex X n) (hm : IsWeight X n m) (hn : 1 ≤ n)
    (hlam : 0 ≤ lam) (hL : LinkTwoSided X m 0 lam)
    (v : meanZeroSpace X m 1) :
    ‖downZero hX hm (upZero hm hn v) - v‖ ≤ lam * ‖v‖ := by
  have hh := nativeError_bound hX hm (k := 0) hn hlam hL v
  have hz := meanZero_zero_level hX hm (downZero hX hm (c := 0) v)
  change ‖downZero hX hm (upZero hm hn v) -
    upZero hm (show 0 ≤ n by omega) (downZero hX hm (c := 0) v) - v‖ ≤ _ at hh
  simpa only [hz, map_zero, sub_zero, Nat.cast_zero, zero_add, one_mul] using hh

end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
namespace HighOrderWalks.TwoSided.Fresh

lemma eps_nonneg (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) : 0 ≤ eps lam k := by
  induction k with
  | zero => simpa [eps] using hlam
  | succ k ih =>
      simp only [eps]
      positivity

lemma scalar_small_delta (r e : ℝ) (hr : 1 ≤ r) (he : 0 ≤ e)
    (h : e ≤ 1 / (2 * (1 + 2 * r * Real.sqrt r))) :
    Real.sqrt r * e ≤ 1 / 4 := by
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hs := Real.sqrt_nonneg r
  have hp : 0 ≤ (r - 1) * Real.sqrt r := mul_nonneg (sub_nonneg.mpr hr) hs
  have hd : 0 < 2 * (1 + 2 * r * Real.sqrt r) := by positivity
  have hden : e * (2 * (1 + 2 * r * Real.sqrt r)) ≤ 1 :=
    (le_div_iff₀ hd).mp h
  have hdom : 4 * Real.sqrt r ≤ 2 * (1 + 2 * r * Real.sqrt r) := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hdom he
  nlinarith

lemma scalar_last_delta (r e : ℝ) (hr : 0 < r)
    (h : e < 1 / (2 * Real.sqrt r)) : Real.sqrt r * e < 1 / 2 := by
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hd : 0 < 2 * Real.sqrt r := by positivity
  have hden := (lt_div_iff₀ hd).mp h
  nlinarith

lemma eps_delta_le_quarter (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ)
    (h : eps lam k ≤ 1 / (2 * (1 + 2 * ((k : ℝ) + 1) *
      Real.sqrt ((k : ℝ) + 1)))) :
    Real.sqrt ((k : ℝ) + 1) * eps lam k ≤ 1 / 4 := by
  apply scalar_small_delta ((k : ℝ) + 1) (eps lam k)
  · have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  · exact eps_nonneg lam hlam k
  · exact h

lemma eps_final_delta_lt_half (lam : ℝ) (hlam : 0 ≤ lam) (n k : ℕ)
    (hk : k + 1 ≤ n)
    (hsmall : ∀ i : ℕ, i + 2 ≤ n →
      eps lam i ≤ 1 / (2 * (1 + 2 * ((i : ℝ) + 1) * Real.sqrt ((i : ℝ) + 1))))
    (hlast : ∀ i : ℕ, i + 1 = n → eps lam i < 1 / (2 * Real.sqrt (n : ℝ))) :
    Real.sqrt ((k : ℝ) + 1) * eps lam k < 1 / 2 := by
  by_cases htop : k + 1 = n
  · have he := hlast k htop
    have hn : (n : ℝ) = (k : ℝ) + 1 := by exact_mod_cast htop.symm
    rw [hn] at he
    exact scalar_last_delta ((k : ℝ) + 1) (eps lam k) (by positivity) he
  · have hi : k + 2 ≤ n := by omega
    have hq := eps_delta_le_quarter lam hlam k (hsmall k hi)
    linarith

lemma eps_final_denominator_pos (lam : ℝ) (hlam : 0 ≤ lam) (n k : ℕ)
    (hk : k + 1 ≤ n)
    (hsmall : ∀ i : ℕ, i + 2 ≤ n →
      eps lam i ≤ 1 / (2 * (1 + 2 * ((i : ℝ) + 1) * Real.sqrt ((i : ℝ) + 1))))
    (hlast : ∀ i : ℕ, i + 1 = n → eps lam i < 1 / (2 * Real.sqrt (n : ℝ))) :
    0 < 1 - Real.sqrt ((k : ℝ) + 1) * eps lam k := by
  have h := eps_final_delta_lt_half lam hlam n k hk hsmall hlast
  linarith

lemma raising_coefficient_domination (r : ℝ) (hr : 1 ≤ r) :
    2 * r * (r + 1) * Real.sqrt r ≤ 2 * r * (1 + 2 * r * Real.sqrt r) := by
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hs := Real.sqrt_nonneg r
  have h1 : 0 ≤ r * (r - 1) * Real.sqrt r :=
    mul_nonneg (mul_nonneg hr0 (sub_nonneg.mpr hr)) hs
  nlinarith

end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

lemma nativeFlagBlocks_piece_mem {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (hk : k ≤ n) (i : Fin (k + 1))
    (x : meanZeroSpace X m (k + 1)) :
    (nativeFlagBlocks hm hk).part i x ∈ flagPiece (levelFlag X m k) i.val :=
  (flagPiece (levelFlag X m k) i.val).starProjection_apply_mem x

lemma native_piece_bound {X : Finset (Finset V)} {n : ℕ} {m : Finset V → ℝ}
    {lam : ℝ} (hX : IsPureComplex X n) (hm : IsWeight X n m) (hlam : 0 ≤ lam)
    (hexp : TwoSidedLSE X m n lam)
    (hsmall : ∀ i : ℕ, i + 2 ≤ n →
      eps lam i ≤ 1 / (2 * (1 + 2 * ((i : ℝ) + 1) * Real.sqrt ((i : ℝ) + 1))))
    (k : ℕ) (hk : k + 1 ≤ n) (j : Fin (k + 1))
    (u : meanZeroSpace X m (k + 1)) (hu : u ∈ flagPiece (levelFlag X m k) j.val) :
    ‖nativeEnergy hX hm hk u - ((k : ℝ) + 1 - (j : ℝ)) • u‖ ≤ eps lam k * ‖u‖ := by
  induction k with
  | zero =>
      have hj : j = 0 := Fin.ext (by have := j.isLt; omega)
      subst j
      simpa only [Nat.cast_zero, Fin.val_zero, zero_add, sub_zero, one_smul, eps, nativeEnergy,
        LinearMap.comp_apply] using native_base_bound hX hm hk hlam (hexp 0 hk) u
  | succ k ih =>
      have he := eps_nonneg lam hlam k
      have hloc := nativeError_bound hX hm hk hlam (hexp (k + 1) hk) u
      by_cases hj : j.val < k + 1
      · have hblock : ∀ i x, ‖nativeEnergy hX hm (show k + 1 ≤ n by omega)
            ((nativeFlagBlocks hm (show k ≤ n by omega)).part i x) -
            ((k : ℝ) + 1 - (i : ℝ)) • (nativeFlagBlocks hm (show k ≤ n by omega)).part i x‖ ≤
            eps lam k * ‖(nativeFlagBlocks hm (show k ≤ n by omega)).part i x‖ := by
          intro i x
          exact ih (by omega) i _ (nativeFlagBlocks_piece_mem hm (by omega) i x)
        have hq := eps_delta_le_quarter lam hlam k (hsmall k (by omega))
        have hr := native_raised_piece hX hm hk he (by linarith) hblock j hj u hu
        have hid : nativeEnergy hX hm hk u - (((k + 1 : ℕ) : ℝ) + 1 - (j : ℝ)) • u =
            nativeError hX hm hk u +
              (upZero hm (show k + 1 ≤ n by omega) (downZero hX hm u) -
                ((k : ℝ) + 1 - (j : ℝ)) • u) := by
          simp only [nativeEnergy, nativeError, LinearMap.sub_apply, LinearMap.comp_apply,
            LinearMap.id_apply, Nat.cast_add, Nat.cast_one]
          module
        rw [hid]
        have hdom := raising_coefficient_domination ((k : ℝ) + 1)
          (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
        calc
          ‖nativeError hX hm hk u + (upZero hm (show k + 1 ≤ n by omega) (downZero hX hm u) -
              ((k : ℝ) + 1 - (j : ℝ)) • u)‖ ≤
              ‖nativeError hX hm hk u‖ + ‖upZero hm (show k + 1 ≤ n by omega) (downZero hX hm u) -
                ((k : ℝ) + 1 - (j : ℝ)) • u‖ := norm_add_le _ _
          _ ≤ (((k + 1 : ℕ) + 1 : ℝ) * lam) * ‖u‖ +
              2 * ((k : ℝ) + 1) * ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 1) * eps lam k * ‖u‖ := add_le_add hloc hr
          _ ≤ (((k + 1 : ℕ) + 1 : ℝ) * lam) * ‖u‖ +
              2 * ((k : ℝ) + 1) * (1 + 2 * ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1)) * eps lam k * ‖u‖ := by
                have hd' : 2 * ((k : ℝ) + 1) * ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 1) ≤
                    2 * ((k : ℝ) + 1) * (1 + 2 * ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1)) := by
                  simpa only [add_assoc, one_add_one_eq_two] using hdom
                exact add_le_add_right
                  (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd' he) (norm_nonneg u)) _
          _ = eps lam (k + 1) * ‖u‖ := by simp only [eps, Nat.cast_add, Nat.cast_one]; ring
      · have hj' : j.val = k + 1 := by omega
        have hz : downZero (c := k + 1) hX hm u = 0 := by
          rw [hj', nativePiece_top_succ hX hm (by omega), LinearMap.mem_ker] at hu
          exact hu
        have hcoef : ((k + 1 : ℕ) : ℝ) + 1 - (j : ℝ) = 1 := by
          rw [hj']; ring
        rw [hcoef, one_smul]
        change ‖nativeEnergy hX hm hk u - upZero hm (show k + 1 ≤ n by omega) (downZero hX hm u) - u‖ ≤ _ at hloc
        rw [hz, map_zero, sub_zero] at hloc
        have hp : 0 ≤ 2 * ((k : ℝ) + 1) * (1 + 2 * ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1)) * eps lam k := by positivity
        simp only [eps, Nat.cast_add, Nat.cast_one] at hloc ⊢
        nlinarith [mul_nonneg hp (norm_nonneg u)]

end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh

lemma upper_eigen_mem_c0 {V : Type*} [DecidableEq V]
    {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hk : k + 1 ≤ n)
    (φ : Finset V → ℝ) (hφ : Supp X (k + 1) φ) (μ : ℝ)
    (heig : upperWalk X m φ = μ • φ) (hμ : μ ≠ 1) :
    φ ∈ c0Module X m (k + 1) := by
  refine ⟨hφ, ?_⟩
  change ip X m (k + 1) φ (fun _ => 1) = 0
  have hmean := upper_mean hX hm hk φ
  have hscale : ip X m (k + 1) (μ • φ) (fun _ => 1) =
      μ * ip X m (k + 1) φ (fun _ => 1) := by
    simp [ip, Finset.mul_sum, mul_left_comm]
  rw [heig, hscale] at hmean
  have hp : (μ - 1) * ip X m (k + 1) φ (fun _ => 1) = 0 := by nlinarith
  exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hμ)

lemma nativeEnergy_eigen {V : Type*} [DecidableEq V]
    {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hk : k + 1 ≤ n)
    (φ : c0Module X m (k + 1)) (μ : ℝ)
    (heig : upperWalk X m φ = μ • (φ : Finset V → ℝ)) :
    nativeEnergy hX hm hk
      (c0WeightedEquiv X m (k + 1) (fun σ hσ => hm.1 σ (mem_cells.mp hσ).1) φ) =
      (((k : ℝ) + 2) * μ) •
      c0WeightedEquiv X m (k + 1) (fun σ hσ => hm.1 σ (mem_cells.mp hσ).1) φ := by
  apply Subtype.ext
  change downLinear X m (k + 1) (upLinear X m (k + 1) (encode X m (k + 1) φ)) =
    (((k : ℝ) + 2) * μ) • encode X m (k + 1) φ
  rw [up_encode X m (k + 1) (fun σ hσ => hm.1 σ (mem_cells.mp hσ).1) φ φ.2.1,
    down_encode X m (k + 1) (fun σ hσ => hm.1 σ (mem_cells.mp hσ).1)
      (dS X φ) (dS_support φ.2.1)]
  ext s
  have hi := upper_identity hm hk s.2 (φ : Finset V → ℝ)
  have he := congrFun heig s
  simp only [Pi.smul_apply, smul_eq_mul] at he
  change Real.sqrt (m s) * dStar X m (dS X φ) s =
    (((k : ℝ) + 2) * μ) * (Real.sqrt (m s) * (φ : Finset V → ℝ) s)
  rw [hi, he]
  push_cast
  ring

end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

lemma nativeVsp_mem_c0 {X : Finset (Finset V)} {n k j : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hk : k ≤ n)
    {f : Finset V → ℝ} (hf : f ∈ Vsp X m k j) : f ∈ c0Module X m (k + 1) := by
  unfold Vsp at hf
  split_ifs at hf with hk0 hj
  · subst k
    exact hf
  · have hi : f ∈ imageLevel X m k j := by
      change ∃ g, g ∈ c0Module X m (j + 1) ∧ ((dSLinear X) ^ (k - j)) g = f
      obtain ⟨g, hg, hgf⟩ := hf
      refine ⟨g, hg, ?_⟩
      rw [Module.End.pow_apply]
      exact hgf
    exact imageLevel_le_c0 hm hk hj.le hi
  · refine ⟨hf.1, ?_⟩
    change ip X m (k + 1) f (fun _ => 1) = 0
    have hz : ip X m k (dStar X m f) (fun _ => 1) = 0 := by
      unfold ip
      apply Finset.sum_eq_zero
      intro τ hτ
      rw [hf.2 τ hτ]
      ring
    rw [dStar_mean hX hm] at hz
    have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hkpos)

lemma nativeUsp_mem_c0 {X : Finset (Finset V)} {n k j : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hk : k ≤ n)
    {f : Finset V → ℝ} (hf : f ∈ Usp X m k j) : f ∈ c0Module X m (k + 1) := by
  unfold Usp at hf
  split_ifs at hf with hj0 hj
  · exact nativeVsp_mem_c0 hX hm hk hf
  · exact nativeVsp_mem_c0 hX hm hk hf.1
  · exact nativeVsp_mem_c0 hX hm hk hf

lemma scaled_interval_iff (d μ a δ : ℝ) (hd : 0 < d) :
    |d * μ - a| ≤ δ ↔ |μ - a / d| ≤ δ / d := by
  have he : d * μ - a = d * (μ - a / d) := by field_simp
  rw [he, abs_mul, abs_of_pos hd, le_div_iff₀ hd]
  constructor <;> intro h <;> nlinarith

end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh

lemma native_projection_transport {V : Type*}
    (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (hm : ∀ σ ∈ cells X c, 0 < m σ)
    (S : Set (Finset V → ℝ)) (U : Submodule ℝ (meanZeroSpace X m c))
    (hU : ∀ w : c0Module X m c, c0WeightedEquiv X m c hm w ∈ U ↔ (w : Finset V → ℝ) ∈ S)
    (φ u : c0Module X m c) (hp : IsWProj X m c S φ u) :
    U.starProjection (c0WeightedEquiv X m c hm φ) = c0WeightedEquiv X m c hm u := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero ((hU u).2 hp.1)
  intro w hw
  obtain ⟨v, rfl⟩ := (c0WeightedEquiv X m c hm).surjective w
  rw [← map_sub, c0WeightedEquiv_inner]
  exact hp.2 v ((hU v).1 hw)

lemma native_projection_error_norm {V : Type*}
    (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (hm : ∀ σ ∈ cells X c, 0 < m σ) (φ u : c0Module X m c) :
    ‖c0WeightedEquiv X m c hm φ - c0WeightedEquiv X m c hm u‖ =
      nrm X m c ((φ : Finset V → ℝ) - (u : Finset V → ℝ)) := by
  simpa only [map_sub, Submodule.coe_sub] using c0WeightedEquiv_norm X m c hm (φ - u)

end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open scoped BigOperators
namespace HighOrderWalks.TwoSided.Fresh

lemma integer_centers_separated {k : ℕ} (i j : Fin (k + 1)) (hij : i ≠ j) :
    1 ≤ |((k : ℝ) + 1 - (i : ℝ)) - ((k : ℝ) + 1 - (j : ℝ))| := by
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · have hh : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hh : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]
    linarith

lemma integer_center_gap {k : ℕ} (i j : Fin (k + 1)) (hij : i ≠ j)
    (ν δ : ℝ) (hj : |ν - ((k : ℝ) + 1 - (j : ℝ))| ≤ δ) :
    1 - δ ≤ |ν - ((k : ℝ) + 1 - (i : ℝ))| := by
  have hs := integer_centers_separated i j hij
  have ht := abs_sub_le ((k : ℝ) + 1 - (i : ℝ)) ν ((k : ℝ) + 1 - (j : ℝ))
  rw [abs_sub_comm ((k : ℝ) + 1 - (i : ℝ)) ν] at ht
  linarith

namespace OrthogonalBlocks
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma cluster_projection {k : ℕ} (P : OrthogonalBlocks (Fin (k + 1)) E)
    (A : E →ₗ[ℝ] E) {e : ℝ} (he : 0 ≤ e)
    (hsmall : Real.sqrt ((k : ℝ) + 1) * e < 1)
    (hblock : ∀ i x, ‖A (P.part i x) - ((k : ℝ) + 1 - (i : ℝ)) • P.part i x‖ ≤ e * ‖P.part i x‖)
    (j : Fin (k + 1)) {ν : ℝ} {x : E} (heig : A x = ν • x)
    (hj : |ν - ((k : ℝ) + 1 - (j : ℝ))| ≤ Real.sqrt ((k : ℝ) + 1) * e) :
    ‖x - P.part j x‖ ≤ (Real.sqrt ((k : ℝ) + 1) * e /
      (1 - Real.sqrt ((k : ℝ) + 1) * e)) * ‖x‖ := by
  let δ := Real.sqrt ((k : ℝ) + 1) * e
  have hg : 0 < 1 - δ := by dsimp [δ]; linarith
  have hr := P.diagonal_residual A (fun i => (k : ℝ) + 1 - (i : ℝ)) he hblock x
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at hr
  have hb := P.complementary_bound (fun i => (k : ℝ) + 1 - (i : ℝ)) j ν x hg.le
    (fun i hij => integer_center_gap i j hij ν δ hj)
  rw [heig] at hr
  have ht : (1 - δ) * ‖x - P.part j x‖ ≤ δ * ‖x‖ := hb.trans hr
  have h : ‖x - P.part j x‖ ≤ (δ * ‖x‖) / (1 - δ) :=
    (le_div_iff₀ hg).2 (by nlinarith [ht])
  change ‖x - P.part j x‖ ≤ δ / (1 - δ) * ‖x‖
  simpa only [div_mul_eq_mul_div] using h

end OrthogonalBlocks
end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

lemma native_diagonal_blocks {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    {lam : ℝ} (hX : IsPureComplex X n) (hm : IsWeight X n m) (hlam : 0 ≤ lam)
    (hexp : TwoSidedLSE X m n lam)
    (hsmall : ∀ i : ℕ, i + 2 ≤ n →
      eps lam i ≤ 1 / (2 * (1 + 2 * ((i : ℝ) + 1) * Real.sqrt ((i : ℝ) + 1))))
    (hk : k + 1 ≤ n) :
    ∀ i x, ‖nativeEnergy hX hm hk ((nativeFlagBlocks hm (show k ≤ n by omega)).part i x) -
      ((k : ℝ) + 1 - (i : ℝ)) • (nativeFlagBlocks hm (show k ≤ n by omega)).part i x‖ ≤
      eps lam k * ‖(nativeFlagBlocks hm (show k ≤ n by omega)).part i x‖ := by
  intro i x
  exact native_piece_bound hX hm hlam hexp hsmall k hk i _ (nativeFlagBlocks_piece_mem hm (by omega) i x)

lemma native_eigen_interval {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    {lam : ℝ} (hX : IsPureComplex X n) (hm : IsWeight X n m) (hlam : 0 ≤ lam)
    (hexp : TwoSidedLSE X m n lam)
    (hsmall : ∀ i : ℕ, i + 2 ≤ n →
      eps lam i ≤ 1 / (2 * (1 + 2 * ((i : ℝ) + 1) * Real.sqrt ((i : ℝ) + 1))))
    (hk : k + 1 ≤ n) (μ : ℝ) (φ : Finset V → ℝ) (hφ : Supp X (k + 1) φ)
    (hφ0 : φ ≠ 0) (heig : upperWalk X m φ = μ • φ) :
    μ = 1 ∨ ∃ j ≤ k, |μ - ((k : ℝ) + 1 - (j : ℝ)) / ((k : ℝ) + 2)| ≤
      Real.sqrt ((k : ℝ) + 1) / ((k : ℝ) + 2) * eps lam k := by
  by_cases hμ : μ = 1
  · exact Or.inl hμ
  right
  let f : c0Module X m (k + 1) := ⟨φ, upper_eigen_mem_c0 hX hm hk φ hφ μ heig hμ⟩
  let e := c0WeightedEquiv X m (k + 1) (fun σ hσ => hm.1 σ (mem_cells.mp hσ).1)
  let P := nativeFlagBlocks hm (show k ≤ n by omega)
  let δ := Real.sqrt ((k : ℝ) + 1) * eps lam k
  have he : 0 ≤ eps lam k := eps_nonneg lam hlam k
  have hδ : 0 ≤ δ := mul_nonneg (Real.sqrt_nonneg _) he
  have herr : ∀ x, ‖nativeEnergy hX hm hk x - P.diagonal (fun i => (k : ℝ) + 1 - (i : ℝ)) x‖ ≤ δ * ‖x‖ := by
    intro x
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, δ] using
      P.diagonal_residual _ _ he (native_diagonal_blocks hX hm hlam hexp hsmall hk) x
  have hv : e f ≠ 0 := by
    intro hz
    have hf : f = 0 := e.injective (hz.trans e.map_zero.symm)
    exact hφ0 (congrArg Subtype.val hf)
  obtain ⟨i, hi⟩ := P.eigenvalue_near_diagonal (nativeEnergy hX hm hk)
    (fun i => (k : ℝ) + 1 - (i : ℝ)) hδ herr hv (nativeEnergy_eigen hX hm hk f μ heig)
  refine ⟨i.val, Nat.le_of_lt_succ i.isLt, ?_⟩
  have hs := (scaled_interval_iff ((k : ℝ) + 2) μ ((k : ℝ) + 1 - (i : ℝ)) δ (by positivity)).1 hi
  convert hs using 1
  dsimp [δ]
  ring

lemma native_projection_bound {X : Finset (Finset V)} {n k j : ℕ} {m : Finset V → ℝ}
    {lam : ℝ} (hX : IsPureComplex X n) (hm : IsWeight X n m) (hlam : 0 ≤ lam)
    (hexp : TwoSidedLSE X m n lam)
    (hsmall : ∀ i : ℕ, i + 2 ≤ n →
      eps lam i ≤ 1 / (2 * (1 + 2 * ((i : ℝ) + 1) * Real.sqrt ((i : ℝ) + 1))))
    (hlast : ∀ i : ℕ, i + 1 = n → eps lam i < 1 / (2 * Real.sqrt (n : ℝ)))
    (hk : k + 1 ≤ n) (hj : j ≤ k) (μ : ℝ) (φ : Finset V → ℝ)
    (hφ : φ ∈ C0 X m (k + 1)) (heig : upperWalk X m φ = μ • φ)
    (hinterval : |μ - ((k : ℝ) + 1 - (j : ℝ)) / ((k : ℝ) + 2)| ≤
      Real.sqrt ((k : ℝ) + 1) / ((k : ℝ) + 2) * eps lam k)
    (u : Finset V → ℝ) (hp : IsWProj X m (k + 1) (Usp X m k j) φ u) :
    nrm X m (k + 1) (φ - u) ≤
      Real.sqrt ((k : ℝ) + 1) * eps lam k / (1 - Real.sqrt ((k : ℝ) + 1) * eps lam k) *
        nrm X m (k + 1) φ := by
  let f : c0Module X m (k + 1) := ⟨φ, hφ⟩
  let u' : c0Module X m (k + 1) := ⟨u, nativeUsp_mem_c0 hX hm (by omega) hp.1⟩
  let e := c0WeightedEquiv X m (k + 1) (fun σ hσ => hm.1 σ (mem_cells.mp hσ).1)
  let P := nativeFlagBlocks hm (show k ≤ n by omega)
  let jj : Fin (k + 1) := ⟨j, by omega⟩
  let U := flagPiece (levelFlag X m k) j
  have hU : ∀ w : c0Module X m (k + 1), e w ∈ U ↔ (w : Finset V → ℝ) ∈ Usp X m k j := by
    intro w
    have hh := nativePiece_decode_iff hX hm (by omega : k ≤ n) hj (e w)
    change e w ∈ U ↔ decode X m (k + 1) (encode X m (k + 1) w) ∈ Usp X m k j at hh
    rwa [decode_encode X m (k + 1) (fun σ hσ => hm.1 σ (mem_cells.mp hσ).1) w w.2.1] at hh
  have hproj := native_projection_transport X m (k + 1)
    (fun σ hσ => hm.1 σ (mem_cells.mp hσ).1) (Usp X m k j) U hU f u' hp
  have hp' : P.part jj (e f) = e u' := hproj
  have hd := eps_final_delta_lt_half lam hlam n k hk hsmall hlast
  have hint : |((k : ℝ) + 2) * μ - ((k : ℝ) + 1 - (jj : ℝ))| ≤
      Real.sqrt ((k : ℝ) + 1) * eps lam k := by
    apply (scaled_interval_iff ((k : ℝ) + 2) μ ((k : ℝ) + 1 - (jj : ℝ)) _ (by positivity)).2
    convert hinterval using 1
    ring
  have hh := P.cluster_projection (nativeEnergy hX hm hk) (eps_nonneg lam hlam k)
    (by linarith) (native_diagonal_blocks hX hm hlam hexp hsmall hk) jj
    (nativeEnergy_eigen hX hm hk f μ heig) hint
  rw [hp'] at hh
  rw [native_projection_error_norm, c0WeightedEquiv_norm] at hh
  exact hh

end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh

lemma sum_supported_pair {α : Type*} [DecidableEq α] (s : Finset α)
    (a b : α) (hab : a ≠ b) (ha : a ∈ s) (hb : b ∈ s)
    (f : α → ℝ) (hf : ∀ x ∈ s, x ≠ a → x ≠ b → f x = 0) :
    ∑ x ∈ s, f x = f a + f b := by
  have hsub : ({a, b} : Finset α) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hsum := Finset.sum_subset hsub (fun x hx hn =>
    hf x hx (by intro h; subst x; simp at hn)
      (by intro h; subst x; simp at hn))
  simpa [hab] using hsum.symm

lemma expansion_parameter_nonneg {V : Type*} [DecidableEq V]
    (X : Finset (Finset V)) (n : ℕ) (hX : IsPureComplex X n)
    (m : Finset V → ℝ) (hm : IsWeight X n m) (lam : ℝ)
    (hexp : TwoSidedLSE X m n lam) (hn : 1 ≤ n) : 0 ≤ lam := by
  obtain ⟨σ, hσ⟩ := hX.2.2.2
  obtain ⟨ρ, hρ, _, hcard⟩ := hX.2.2.1 σ hσ
  have htwo : 1 < ρ.card := by omega
  obtain ⟨u, huρ, v, hvρ, huv⟩ := Finset.one_lt_card.mp htwo
  have hu : ({u} : Finset V) ∈ X := hX.1 ρ hρ _ (Finset.singleton_subset_iff.mpr huρ)
  have hv : ({v} : Finset V) ∈ X := hX.1 ρ hρ _ (Finset.singleton_subset_iff.mpr hvρ)
  have huv' : ({u} : Finset V) ≠ {v} := by simpa using huv
  have huc : ({u} : Finset V) ∈ cells X 1 := mem_cells.mpr ⟨hu, by simp⟩
  have hvc : ({v} : Finset V) ∈ cells X 1 := mem_cells.mpr ⟨hv, by simp⟩
  have hempty : (∅ : Finset V) ∈ cells X 0 :=
    mem_cells.mpr ⟨hX.1 ρ hρ _ (Finset.empty_subset _), by simp⟩
  have hlink : link X (∅ : Finset V) = X := by
    ext τ
    simp [link]
  have hweight : linkWeight m (∅ : Finset V) = m := by
    funext τ
    simp [linkWeight]
  let g : Finset V → ℝ := fun τ => if τ = {u} then m {v} else if τ = {v} then -m {u} else 0
  have hgu : g {u} = m {v} := by simp [g]
  have hgv : g {v} = -m {u} := by simp [g, huv'.symm]
  have hgz : ∀ τ, τ ≠ {u} → τ ≠ {v} → g τ = 0 := by
    intro τ hτu hτv
    simp [g, hτu, hτv]
  have hmean : ip X m 1 g (fun _ => 1) = 0 := by
    unfold ip
    rw [sum_supported_pair (cells X 1) {u} {v} huv' huc hvc
      (fun τ => m τ * g τ * 1) (by
        intro τ _ hτu hτv
        simp [hgz τ hτu hτv])]
    rw [hgu, hgv]
    ring
  have hnorm : ip X m 1 g g = m {u} * m {v} * m {v} +
      m {v} * (-m {u}) * (-m {u}) := by
    unfold ip
    rw [sum_supported_pair (cells X 1) {u} {v} huv' huc hvc
      (fun τ => m τ * g τ * g τ) (by
        intro τ _ hτu hτv
        simp [hgz τ hτu hτv])]
    rw [hgu, hgv]
  have hmu : 0 < m {u} := hm.1 _ hu
  have hmv : 0 < m {v} := hm.1 _ hv
  have hpos : 0 < ip X m 1 g g := by
    rw [hnorm]
    have hp : 0 < m {u} * m {v} * m {v} := by positivity
    have hq : 0 ≤ m {v} * (-m {u}) * (-m {u}) := by
      have hh := mul_nonneg (le_of_lt hmv) (sq_nonneg (m {u}))
      nlinarith
    linarith
  have hlocal := hexp 0 hn ∅ hempty g
  rw [hlink, hweight] at hlocal
  have h := hlocal hmean
  have hprod : 0 ≤ lam * ip X m 1 g g := le_trans (abs_nonneg _) h
  exact nonneg_of_mul_nonneg_left hprod hpos

end HighOrderWalks.TwoSided.Fresh
end

section

noncomputable section
namespace HighOrderWalks.TwoSided.Fresh
theorem native_theorem_5_9 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : HighOrderWalks.OneSided.IsPureComplex X n) (m : Finset V → ℝ) (hm : HighOrderWalks.OneSided.IsWeight X n m)
    (lam : ℝ) (hexp : TwoSidedLSE X m n lam)
    (hsmall : ∀ k : ℕ, k + 2 ≤ n →
      eps lam k ≤ 1 / (2 * (1 + 2 * ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1))))
    (hlast : ∀ k : ℕ, k + 1 = n → eps lam k < 1 / (2 * Real.sqrt (n : ℝ))) :
    ∀ k : ℕ, k + 1 ≤ n →
      (∀ μ : ℝ, ∀ φ : Finset V → ℝ, Supp X (k + 1) φ → φ ≠ 0 → HighOrderWalks.OneSided.upperWalk X m φ = μ • φ →
        μ = 1 ∨ ∃ j ≤ k, |μ - ((k : ℝ) + 1 - (j : ℝ)) / ((k : ℝ) + 2)| ≤
          Real.sqrt ((k : ℝ) + 1) / ((k : ℝ) + 2) * eps lam k) ∧
      (∀ j ≤ k, ∀ μ : ℝ, ∀ φ ∈ C0 X m (k + 1), HighOrderWalks.OneSided.upperWalk X m φ = μ • φ →
        |μ - ((k : ℝ) + 1 - (j : ℝ)) / ((k : ℝ) + 2)| ≤
          Real.sqrt ((k : ℝ) + 1) / ((k : ℝ) + 2) * eps lam k →
        ∀ u : Finset V → ℝ, IsWProj X m (k + 1) (Usp X m k j) φ u →
          HighOrderWalks.OneSided.nrm X m (k + 1) (φ - u) ≤
            Real.sqrt ((k : ℝ) + 1) * eps lam k / (1 - Real.sqrt ((k : ℝ) + 1) * eps lam k) *
              HighOrderWalks.OneSided.nrm X m (k + 1) φ) := by
  intro k hk
  have hlam : 0 ≤ lam := expansion_parameter_nonneg X n hX m hm lam hexp (by omega)
  constructor
  · intro μ φ hφ hφ0 heig
    exact native_eigen_interval hX hm hlam hexp hsmall hk μ φ hφ hφ0 heig
  · intro j hj μ φ hφ heig hi u hu
    exact native_projection_bound hX hm hlam hexp hsmall hlast hk hj μ φ hφ heig hi u hu

end HighOrderWalks.TwoSided.Fresh
end

open HighOrderWalks.TwoSided

theorem solution {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : HighOrderWalks.OneSided.IsPureComplex X n) (m : Finset V → ℝ) (hm : HighOrderWalks.OneSided.IsWeight X n m)
    (lam : ℝ) (hexp : TwoSidedLSE X m n lam)
    (hsmall : ∀ k : ℕ, k + 2 ≤ n →
      eps lam k ≤ 1 / (2 * (1 + 2 * ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1))))
    (hlast : ∀ k : ℕ, k + 1 = n → eps lam k < 1 / (2 * Real.sqrt (n : ℝ))) :
    ∀ k : ℕ, k + 1 ≤ n →
      (∀ μ : ℝ, ∀ φ : Finset V → ℝ, Supp X (k + 1) φ → φ ≠ 0 → HighOrderWalks.OneSided.upperWalk X m φ = μ • φ →
        μ = 1 ∨ ∃ j ≤ k, |μ - ((k : ℝ) + 1 - (j : ℝ)) / ((k : ℝ) + 2)| ≤
          Real.sqrt ((k : ℝ) + 1) / ((k : ℝ) + 2) * eps lam k) ∧
      (∀ j ≤ k, ∀ μ : ℝ, ∀ φ ∈ C0 X m (k + 1), HighOrderWalks.OneSided.upperWalk X m φ = μ • φ →
        |μ - ((k : ℝ) + 1 - (j : ℝ)) / ((k : ℝ) + 2)| ≤
          Real.sqrt ((k : ℝ) + 1) / ((k : ℝ) + 2) * eps lam k →
        ∀ u : Finset V → ℝ, IsWProj X m (k + 1) (Usp X m k j) φ u →
          HighOrderWalks.OneSided.nrm X m (k + 1) (φ - u) ≤
            Real.sqrt ((k : ℝ) + 1) * eps lam k / (1 - Real.sqrt ((k : ℝ) + 1) * eps lam k) *
              HighOrderWalks.OneSided.nrm X m (k + 1) φ) := by
  exact Fresh.native_theorem_5_9 X n hX m hm lam hexp hsmall hlast
