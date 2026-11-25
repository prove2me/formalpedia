-- Prove2me | solution 1 for GlobalTheory.DefinitePacking.dualPack
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:18:24.186067+00:00
-- url     : https://prove2.me/submissions/a29abf9a-7327-4564-a9c3-8ddde19b435b

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OneLeNormMulAbsNormSq
import Theorems.Thm_GlobalTheory_DefinitePacking_exists_diag
import Theorems.Thm_GlobalTheory_DefinitePacking_one_le_norm_mul_absNorm_sq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HermitianLatticeCounting_Final_LatticeSumBounds_boxCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
open GlobalTheory GlobalTheory.DefinitePacking
namespace GlobalTheory.DefinitePacking
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (ι : Type) [Fintype ι] (τ : ι → (K →+* ℂ)) (S : Submodule (𝓞 K) V) (I : Ideal (𝓞 K)) (s : ℕ) (ρ : ι → ℝ), h.IsSymm → (∀ v a, τ v (star a) = starRingEnd ℂ (τ v a)) → (∀ a : K, ∏ v, ‖τ v a‖ ^ 2 = |((Algebra.norm ℚ a : ℚ) : ℝ)|) → (∀ v, ∀ x : V, x ≠ 0 → 0 < (τ v (h x x)).re) → Nonempty ι → finrank K (Submodule.span K (S : Set V)) = s → I ≠ ⊥ → (∀ x ∈ I • S, ∀ y ∈ I • S, ∃ o : 𝓞 K, (o : K) = h x y) → (∀ v, 0 < ρ v) → {x | x ∈ S ∧ ∀ v, (τ v (h x x)).re ≤ ρ v}.Finite ∧ ({x | x ∈ S ∧ ∀ v, (τ v (h x x)).re ≤ ρ v}.ncard : ℝ) ≤ 9 ^ (s * Fintype.card ι) * (max 1 ((Ideal.absNorm I : ℝ) * ∏ v, ρ v)) ^ s := by
  intro K V _ _ _ _ _ _ _ _ h ι _ τ S I s ρ hs hτ hN hpos hne hrk hI hint hρ
  obtain ⟨v₀⟩ := hne
  have ha : ∀ x : V, x ≠ 0 → h x x ≠ 0 := by
    intro x hx h0
    have := hpos v₀ x hx
    simp [h0] at this
  have hnn : ∀ v x, 0 ≤ (τ v (h x x)).re := by
    intro v x
    by_cases hx : x = 0
    · simp [hx]
    · exact (hpos v x hx).le
  have hreal : ∀ v x, τ v (h x x) = ((τ v (h x x)).re : ℂ) := by
    intro v x
    have h1 : star (h x x) = h x x := hs.eq x x
    have h2 := hτ v (h x x)
    rw [h1] at h2
    exact (Complex.conj_eq_iff_re.mp h2.symm).symm
  obtain ⟨f, e, hf⟩ := exists_diag h hs ha s (Submodule.span K (S : Set V)) hrk.le
  let Φ : V →+ (ι → EuclideanSpace ℂ (Fin s)) :=
    { toFun := fun x v => WithLp.toLp 2 fun i =>
        τ v (f i x) * (Real.sqrt (τ v (h (e i) (e i))).re : ℂ)
      map_zero' := by ext v i; simp
      map_add' := by intro x y; ext v i; simp [add_mul] }
  have hΦ : ∀ x ∈ S, ∀ v, ‖Φ x v‖ ^ 2 = (τ v (h x x)).re := by
    intro x hx v
    rw [EuclideanSpace.norm_sq_eq, hf x (Submodule.subset_span hx), map_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change ‖τ v (f i x) * (Real.sqrt (τ v (h (e i) (e i))).re : ℂ)‖ ^ 2 = _
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hnn _ _),
      map_mul, map_mul, hτ, ← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul,
      Complex.normSq_eq_norm_sq]
  have hinj : Set.InjOn Φ S := by
    intro x hx y hy hxy
    by_contra hne
    have h1 := hpos v₀ (x - y) (sub_ne_zero.mpr hne)
    rw [← hΦ _ (S.sub_mem hx hy), map_sub, hxy] at h1
    simp at h1
  have hIpos : (0 : ℝ) < (Ideal.absNorm I : ℝ) := by
    have : Ideal.absNorm I ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hI
    positivity
  have hlow : ∀ x ∈ S, x ≠ 0 → (Ideal.absNorm I : ℝ)⁻¹ ≤ ∏ v, (τ v (h x x)).re := by
    intro x hx hx0
    have h1 := one_le_norm_mul_absNorm_sq (h x x) (ha x hx0) I hI (by
      intro a ha b hb
      obtain ⟨o, ho⟩ := hint _ (Submodule.smul_mem_smul ha hx) _ (Submodule.smul_mem_smul hb hx)
      refine ⟨o, ?_⟩
      rw [ho, ← algebraMap_smul K a x, ← algebraMap_smul K b x]
      simp only [map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        starRingEnd_apply]
      change (b : K) * (star (a : K) * h x x) = _
      ring)
    have h2 : |((Algebra.norm ℚ (h x x) : ℚ) : ℝ)| = (∏ v, (τ v (h x x)).re) ^ 2 := by
      rw [← hN, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [hreal v x, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs, sq_abs]
    have h3 : 0 ≤ ∏ v, (τ v (h x x)).re := Finset.prod_nonneg fun v _ => hnn v x
    rw [h2, ← mul_pow] at h1
    have h4 : 1 ≤ (∏ v, (τ v (h x x)).re) * (Ideal.absNorm I : ℝ) :=
      (one_le_sq_iff₀ (by positivity)).mp h1
    rw [inv_eq_one_div, div_le_iff₀ hIpos]
    exact h4
  obtain ⟨hfin, hcard⟩ := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.boxCount ι s (S.toAddSubgroup.map Φ)
    (Ideal.absNorm I : ℝ)⁻¹ (fun v => Real.sqrt (ρ v)) (inv_pos.mpr hIpos)
    (fun v => Real.sqrt_pos.mpr (hρ v)) (by
      rintro _ ⟨x, hx, rfl⟩ hx0
      have hx0' : x ≠ 0 := by rintro rfl; exact hx0 (map_zero Φ)
      rw [Finset.prod_congr rfl fun v _ => hΦ x hx v]
      exact hlow x hx hx0')
  have hset : {x | x ∈ S.toAddSubgroup.map Φ ∧ ∀ v, ‖x v‖ ≤ Real.sqrt (ρ v)}
      = Φ '' {x | x ∈ S ∧ ∀ v, (τ v (h x x)).re ≤ ρ v} := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hy⟩
      refine ⟨x, ⟨hx, fun v => ?_⟩, rfl⟩
      rw [← hΦ x hx v]
      exact (Real.le_sqrt (norm_nonneg _) (hρ v).le).mp (hy v)
    · rintro ⟨x, ⟨hx, hy⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, fun v => ?_⟩
      apply Real.le_sqrt_of_sq_le
      rw [hΦ x hx v]
      exact hy v
  have hinj' : Set.InjOn Φ {x | x ∈ S ∧ ∀ v, (τ v (h x x)).re ≤ ρ v} :=
    hinj.mono fun x hx => hx.1
  rw [hset] at hfin hcard
  refine ⟨Set.Finite.of_finite_image hfin hinj', ?_⟩
  rw [hinj'.ncard_image, Finset.prod_congr rfl fun v _ => Real.sq_sqrt (hρ v).le,
    div_inv_eq_mul, mul_comm (∏ v, ρ v)] at hcard
  exact hcard
end GlobalTheory.DefinitePacking
