-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.left_of_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:41:23.290799+00:00
-- url     : https://prove2.me/submissions/d3ed9fc8-a5f9-4cf5-999e-4956cab079a1

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistB
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_ind_mem
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_ind_index
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_ind_zero
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_sb_unif


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology GlobalTheory.WeilM
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
namespace GlobalTheory.ThK.Dbl.LD
theorem _root_.solution (χ : G →* ℂ) (θ : G →* G) (cθ : Continuous θ) (iθ : ∀ x, θ (θ x) = x) {g : G} (hg : θ g = g⁻¹)
    (l : (G → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ φ ∈ SB G, ∀ h, l (fun x => φ (x * h)) = χ h * l φ) {φ : G → ℂ} (hφ : φ ∈ SB G) :
    l (fun x => φ (g * x)) = χ g * l φ := by
  classical
  by_cases h0 : φ = 0
  · subst h0; exact (map_zero l).trans (by rw [map_zero, mul_zero])
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 h0
  let K₀ : Subgroup G :=
    { carrier := {k | ∀ x, φ (k * x) = φ x}
      one_mem' := fun x => by rw [one_mul]
      mul_mem' := fun {a b} ha hb x => by rw [mul_assoc, ha, hb]
      inv_mem' := fun {a} ha x => by rw [← ha, mul_inv_cancel_left] }
  have o₀ : IsOpen (K₀ : Set G) := by
    refine K₀.isOpen_of_mem_nhds (g := 1) ?_
    filter_upwards [sb_unif hφ (fun k x => k * x) (1 : G) (by fun_prop) one_mul,
      sb_unif hφ (fun k x => k⁻¹ * x) (1 : G) (by fun_prop) (by simp)] with k h1 h2 x
    by_cases hx : x ∈ tsupport φ
    · exact h1 x hx
    · by_cases hx' : k * x ∈ tsupport φ
      · simpa using (h2 _ hx').symm
      · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']
  have c₀ : IsCompact (K₀ : Set G) :=
    (IsCompact.image hφ.2 (continuous_mul_right x₀⁻¹)).of_isClosed_subset (K₀.isClosed_of_isOpen o₀) fun k hk =>
      ⟨k * x₀, subset_tsupport _ (by rw [Function.mem_support, hk x₀]; exact hx₀), by simp⟩
  let K := K₀ ⊓ K₀.comap θ
  have o : IsOpen (K : Set G) := o₀.inter (o₀.preimage cθ)
  have c : IsCompact (K : Set G) := c₀.of_isClosed_subset (K.isClosed_of_isOpen o) fun k hk => hk.1
  have hθ : ∀ x, θ x ∈ K ↔ x ∈ K := fun x => by
    show θ x ∈ K₀ ∧ θ (θ x) ∈ K₀ ↔ x ∈ K₀ ∧ θ x ∈ K₀
    rw [iθ]; exact and_comm
  let K' := K.comap (MulAut.conj g).toMonoidHom
  have hK' : ∀ x, x ∈ K' ↔ g * x * g⁻¹ ∈ K := fun x => Iff.rfl
  have hs : ind K' = fun x => ind K (g * x * g⁻¹) := rfl
  have o' : IsOpen (K' : Set G) := o.preimage (f := fun x => g * x * g⁻¹) (by fun_prop)
  have c' : IsCompact (K' : Set G) := (c.image (f := fun x => g⁻¹ * x * g) (by fun_prop)).of_isClosed_subset
    (K'.isClosed_of_isOpen o') fun x hx => ⟨_, (hK' x).1 hx, by group⟩
  have hconj : ∀ x, χ (g * x * g⁻¹) = χ x := fun x => by
    rw [map_mul, map_mul, mul_comm (χ g), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have key : l (ind K') = l (ind K) := by
    by_cases hχ : ∀ k ∈ K, χ k = 1
    · have hχ' : ∀ k ∈ K', χ k = 1 := fun k hk => by rw [← hconj, hχ _ ((hK' k).1 hk)]
      rw [ind_index χ l hl (inf_le_left : K ⊓ K' ≤ K) (o.inter o') c hχ,
        ind_index χ l hl (inf_le_right : K ⊓ K' ≤ K') (o.inter o') c' hχ', Subgroup.inf_relIndex_left,
        Subgroup.inf_relIndex_right]
      let α := θ.comp (MulAut.conj g).toMonoidHom
      have hα : ∀ x, α x = θ (g * x * g⁻¹) := fun _ => rfl
      have e1 : K.comap α = K' := by ext x; rw [Subgroup.mem_comap, hα, hθ, hK']
      have e2 : K.map α = K' := by
        ext x
        rw [Subgroup.mem_map, hK']
        constructor
        · rintro ⟨y, hy, rfl⟩
          rw [hα, map_mul, map_mul, map_inv, hg]; simpa [mul_assoc] using (hθ y).2 hy
        · intro hx
          refine ⟨_, (hθ _).2 hx, ?_⟩
          rw [hα, map_mul, map_mul, map_inv, hg, iθ]; group
      conv_rhs => rw [← e1, Subgroup.relIndex_comap, e2, e1]
    · push Not at hχ
      obtain ⟨k, hk, hχ⟩ := hχ
      rw [ind_zero χ l hl o c hk hχ, ind_zero χ l hl o' c' (k := g⁻¹ * k * g) ((hK' _).2 (by simpa [mul_assoc] using hk))]
      rw [← hconj]; simpa [mul_assoc] using hχ
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology o
  have hfin : ((fun x : G => ((x⁻¹ : G) : G ⧸ K)) '' tsupport φ).Finite :=
    (IsCompact.image hφ.2 (QuotientGroup.continuous_mk.comp continuous_inv)).finite_of_discrete
  have hmem : ∀ (x : G) (q : G ⧸ K), x * q.out ∈ (K : Set G) ↔ ((x⁻¹ : G) : G ⧸ K) = q := by
    intro x q
    conv_rhs => rw [← QuotientGroup.out_eq' q, QuotientGroup.eq, inv_inv]
    rfl
  have dec : ∀ x, φ x = ∑ q ∈ hfin.toFinset, φ q.out⁻¹ * ind K (x * q.out) := fun x => by
    have hx : φ ((x⁻¹ : G) : G ⧸ K).out⁻¹ = φ x := by
      rw [← ((hmem x _).2 rfl).1, mul_inv_cancel_right]
    rw [Finset.sum_eq_single ((x⁻¹ : G) : G ⧸ K)]
    · rw [ind, Set.indicator_of_mem ((hmem x _).2 rfl), hx, mul_one]
    · intro q _ hq
      rw [ind, Set.indicator_of_notMem (fun h => hq ((hmem x q).1 h).symm), mul_zero]
    · intro h
      rw [hx, image_eq_zero_of_notMem_tsupport (f := φ) (x := x), zero_mul]
      exact fun hs => h (hfin.mem_toFinset.2 ⟨_, hs, rfl⟩)
  have d1 : φ = ∑ q ∈ hfin.toFinset, φ q.out⁻¹ • fun x => ind K (x * q.out) := by
    ext x; rw [dec x]; simp
  have d2 : (fun x => φ (g * x)) = ∑ q ∈ hfin.toFinset, φ q.out⁻¹ • fun x => ind K' (x * (q.out * g)) := by
    ext x; rw [dec, hs]; simp [mul_assoc]
  rw [d2]
  conv_rhs => rw [d1]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul, map_smul, hl _ (ind_mem o' c'), hl _ (ind_mem o c), key, map_mul, smul_eq_mul, smul_eq_mul]
  ring
end GlobalTheory.ThK.Dbl.LD
