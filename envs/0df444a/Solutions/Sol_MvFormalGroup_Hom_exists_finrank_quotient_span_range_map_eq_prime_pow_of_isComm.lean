-- Prove2me | solution 1 for MvFormalGroup.Hom.exists_finrank_quotient_span_range_map_eq_prime_pow_of_isComm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/8516f368-2d17-5db9-afe6-f331c872cda6

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Theorems.Thm_MvFormalGroup_Hom_exists_comp_eq_and_comp_eq_X_pow_and_finrank_eq_pow_mul
import Theorems.Thm_MvPowerSeries_exists_algEquiv_tensorProduct_quotient_span_map_of_pow_span_X_le
import Theorems.Thm_MvPowerSeries_span_range_X_eq_ker_constantCoeff
import Theorems.Thm_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_Hom_exists_finrank_quotient_span_range_map_eq_prime_pow_of_isComm
p2m_attr_erase "instance" "MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'"

set_option autoImplicit false

noncomputable section

universe u

namespace P2mKcKernelOrder

open MvPowerSeries

variable {k : Type u} [Field k] {d : ℕ}

def mX (k : Type u) [Field k] (d : ℕ) : Ideal (MvPowerSeries (Fin d) k) :=
  Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) k))

theorem mX_eq_ker : mX k d = RingHom.ker (constantCoeff : MvPowerSeries (Fin d) k →+* k) :=
  MvPowerSeries.span_range_X_eq_ker_constantCoeff d

theorem mem_mX_iff (f : MvPowerSeries (Fin d) k) : f ∈ mX k d ↔ constantCoeff f = 0 := by
  rw [mX_eq_ker, RingHom.mem_ker]

theorem constantCoeff_surjective :
    Function.Surjective (constantCoeff : MvPowerSeries (Fin d) k →+* k) :=
  fun a => ⟨C a, constantCoeff_C a⟩

theorem mX_isMaximal : (mX k d).IsMaximal := by
  rw [mX_eq_ker]
  exact RingHom.ker_isMaximal_of_surjective _ constantCoeff_surjective

theorem mX_ne_top : mX k d ≠ ⊤ := mX_isMaximal.ne_top

theorem mX_eq_maximalIdeal : mX k d = IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) k) :=
  IsLocalRing.eq_maximalIdeal mX_isMaximal

theorem span_le_mX {ι : Type*} (g : ι → MvPowerSeries (Fin d) k)
    (hg : ∀ i, constantCoeff (g i) = 0) : Ideal.span (Set.range g) ≤ mX k d := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact (mem_mX_iff _).2 (hg i)

theorem exists_pow_mX_le (J : Ideal (MvPowerSeries (Fin d) k))
    [hfin : Module.Finite k (MvPowerSeries (Fin d) k ⧸ J)] : ∃ N : ℕ, mX k d ^ N ≤ J := by
  classical
  set R := MvPowerSeries (Fin d) k ⧸ J
  haveI : IsArtinianRing R := IsArtinianRing.of_finite k R
  obtain ⟨N, hN⟩ := (IsArtinianRing.isNilpotent_jacobson_bot (R := R))
  refine ⟨N, ?_⟩

  have hle : (mX k d).map (Ideal.Quotient.mk J) ≤ (⊥ : Ideal R).jacobson := by
    refine le_sInf ?_
    rintro M ⟨-, hM⟩
    haveI := hM
    have hc : (Ideal.comap (Ideal.Quotient.mk J) M).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    have hEq : Ideal.comap (Ideal.Quotient.mk J) M = mX k d := by
      rw [IsLocalRing.eq_maximalIdeal hc, mX_eq_maximalIdeal]
    rw [Ideal.map_le_iff_le_comap, hEq]
  have hbot : ((mX k d) ^ N).map (Ideal.Quotient.mk J) = ⊥ := by
    rw [Ideal.map_pow]
    have h := Ideal.pow_right_mono hle N
    rw [hN, Ideal.zero_eq_bot] at h
    exact le_bot_iff.1 h
  rwa [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at hbot

theorem exists_eq_single_of_degree_eq_one (n : Fin d →₀ ℕ) (hn : n.degree = 1) :
    ∃ i, n = Finsupp.single i 1 := by
  classical
  have hne : n ≠ 0 := by
    intro h
    rw [h, map_zero] at hn
    exact zero_ne_one hn
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (Finsupp.ext h)
  refine ⟨i, ?_⟩
  have hi1 : n i = 1 := by
    have := Finsupp.le_degree i n
    rw [hn] at this
    omega
  ext j
  by_cases hj : j = i
  · subst hj
    rw [hi1, Finsupp.single_eq_same]
  · rw [Finsupp.single_eq_of_ne hj]
    by_contra hj0
    have h2 : n i + n j ≤ n.degree := by
      rw [Finsupp.degree_eq_sum]
      calc n i + n j = ∑ l ∈ ({i, j} : Finset (Fin d)), n l := by
            rw [Finset.sum_pair (Ne.symm hj)]
        _ ≤ ∑ l, n l := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            intro _ _ _
            exact Nat.zero_le _
    rw [hn, hi1] at h2
    omega

def linForm (g : Fin d → MvPowerSeries (Fin d) k) (j : Fin d) : MvPowerSeries (Fin d) k :=
  ∑ i, MvFormalGroup.linearPart g j i • (X i : MvPowerSeries (Fin d) k)

theorem coeff_linForm (g : Fin d → MvPowerSeries (Fin d) k) (j : Fin d) (n : Fin d →₀ ℕ) :
    coeff n (linForm g j) =
      ∑ i, if n = Finsupp.single i 1 then MvFormalGroup.linearPart g j i else 0 := by
  classical
  simp only [linForm, map_sum, map_smul, coeff_X, smul_eq_mul, mul_ite, mul_one, mul_zero]

theorem sub_linForm_mem (g : Fin d → MvPowerSeries (Fin d) k) (hg : ∀ i, constantCoeff (g i) = 0)
    (j : Fin d) : g j - linForm g j ∈ mX k d ^ 2 := by
  classical
  refine MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero 2 _ fun n hn => ?_
  rw [map_sub, coeff_linForm, sub_eq_zero]
  have hcases : n.degree = 0 ∨ n.degree = 1 := by omega
  rcases hcases with h0 | h1
  · rw [Finsupp.degree_eq_zero_iff] at h0
    subst h0
    rw [coeff_zero_eq_constantCoeff_apply, hg]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    intro h
    have h1 : (0 : Fin d →₀ ℕ) i = (Finsupp.single i 1 : Fin d →₀ ℕ) i := by rw [h]
    rw [Finsupp.zero_apply, Finsupp.single_eq_same] at h1
    exact zero_ne_one h1
  · obtain ⟨i₀, rfl⟩ := exists_eq_single_of_degree_eq_one n h1
    have hs : ∀ i, (Finsupp.single i₀ 1 = Finsupp.single i 1) ↔ i₀ = i := fun i =>
      ⟨fun h => Finsupp.single_left_injective one_ne_zero h, fun h => by rw [h]⟩
    simp only [hs, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl

theorem mX_le_sup_sq (g : Fin d → MvPowerSeries (Fin d) k) (hg : ∀ i, constantCoeff (g i) = 0)
    (hu : IsUnit (MvFormalGroup.linearPart g)) :
    mX k d ≤ Ideal.span (Set.range g) ⊔ mX k d ^ 2 := by
  classical
  set L := MvFormalGroup.linearPart g with hL
  set J := Ideal.span (Set.range g)

  have hlin : ∀ j, linForm g j ∈ J ⊔ mX k d ^ 2 := by
    intro j
    have h1 : g j ∈ J ⊔ mX k d ^ 2 := Ideal.mem_sup_left (Ideal.subset_span ⟨j, rfl⟩)
    have h2 : g j - linForm g j ∈ J ⊔ mX k d ^ 2 := Ideal.mem_sup_right (sub_linForm_mem g hg j)
    have := Submodule.sub_mem _ h1 h2
    rwa [sub_sub_cancel] at this

  obtain ⟨Lu, hLu⟩ := hu
  have hinv : (↑Lu⁻¹ : Matrix (Fin d) (Fin d) k) * L = 1 := by rw [← hLu, Units.inv_mul]
  have hX : ∀ l, (X l : MvPowerSeries (Fin d) k) =
      ∑ j, (↑Lu⁻¹ : Matrix (Fin d) (Fin d) k) l j • linForm g j := by
    intro l
    calc (X l : MvPowerSeries (Fin d) k)
        = ∑ i, ((↑Lu⁻¹ : Matrix (Fin d) (Fin d) k) * L) l i • (X i : MvPowerSeries (Fin d) k) := by
          rw [hinv, Finset.sum_eq_single l]
          · rw [Matrix.one_apply_eq, one_smul]
          · intro i _ hi
            rw [Matrix.one_apply_ne (Ne.symm hi), zero_smul]
          · intro h
            exact absurd (Finset.mem_univ l) h
      _ = ∑ i, ∑ j, ((↑Lu⁻¹ : Matrix (Fin d) (Fin d) k) l j * L j i) •
            (X i : MvPowerSeries (Fin d) k) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Matrix.mul_apply, Finset.sum_smul]
      _ = ∑ j, ∑ i, ((↑Lu⁻¹ : Matrix (Fin d) (Fin d) k) l j * L j i) •
            (X i : MvPowerSeries (Fin d) k) := Finset.sum_comm
      _ = ∑ j, (↑Lu⁻¹ : Matrix (Fin d) (Fin d) k) l j • linForm g j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [linForm, Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul]
  rw [mX, Ideal.span_le]
  rintro _ ⟨l, rfl⟩
  rw [SetLike.mem_coe, hX l]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ _ (hlin j)

theorem mX_le_sup_pow (g : Fin d → MvPowerSeries (Fin d) k) (hg : ∀ i, constantCoeff (g i) = 0)
    (hu : IsUnit (MvFormalGroup.linearPart g)) (n : ℕ) :
    mX k d ≤ Ideal.span (Set.range g) ⊔ mX k d ^ (n + 2) := by
  set J := Ideal.span (Set.range g)
  induction n with
  | zero => exact mX_le_sup_sq g hg hu
  | succ n ih =>
    have hsq : mX k d ^ 2 ≤ J ⊔ mX k d ^ (n + 3) := by
      calc mX k d ^ 2 = mX k d * mX k d := pow_two _
        _ ≤ mX k d * (J ⊔ mX k d ^ (n + 2)) := Ideal.mul_mono_right ih
        _ = mX k d * J ⊔ mX k d ^ (n + 3) := by rw [Ideal.mul_sup, ← pow_succ']
        _ ≤ J ⊔ mX k d ^ (n + 3) := sup_le_sup_right Ideal.mul_le_right _
    calc mX k d ≤ J ⊔ mX k d ^ 2 := mX_le_sup_sq g hg hu
      _ ≤ J ⊔ (J ⊔ mX k d ^ (n + 3)) := sup_le_sup_left hsq _
      _ = J ⊔ mX k d ^ (n + 1 + 2) := by rw [← sup_assoc, sup_idem]

theorem span_eq_mX (g : Fin d → MvPowerSeries (Fin d) k) (hg : ∀ i, constantCoeff (g i) = 0)
    (hu : IsUnit (MvFormalGroup.linearPart g))
    [Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g))] :
    Ideal.span (Set.range g) = mX k d := by
  refine le_antisymm (span_le_mX g hg) ?_
  obtain ⟨N, hN⟩ := exists_pow_mX_le (Ideal.span (Set.range g))
  calc mX k d ≤ Ideal.span (Set.range g) ⊔ mX k d ^ (N + 2) := mX_le_sup_pow g hg hu N
    _ ≤ Ideal.span (Set.range g) ⊔ mX k d ^ N :=
        sup_le_sup_left (Ideal.pow_le_pow_right (by omega)) _
    _ = Ideal.span (Set.range g) := sup_eq_left.2 hN

def ccAlgHom (k : Type u) [Field k] (d : ℕ) : MvPowerSeries (Fin d) k →ₐ[k] k :=
  { (constantCoeff : MvPowerSeries (Fin d) k →+* k) with
    commutes' := fun a => by
      show constantCoeff (algebraMap k (MvPowerSeries (Fin d) k) a) = a
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        constantCoeff_C] }

theorem finrank_quotient_mX : Module.finrank k (MvPowerSeries (Fin d) k ⧸ mX k d) = 1 := by
  have hker : mX k d = RingHom.ker (ccAlgHom k d) := by
    rw [mX_eq_ker]
    ext f
    simp only [RingHom.mem_ker]
    rfl
  have hsurj : Function.Surjective (ccAlgHom k d) := fun a => ⟨C a, constantCoeff_C a⟩
  let e₁ := Ideal.quotientEquivAlgOfEq k hker
  let e₂ := Ideal.quotientKerAlgEquivOfSurjective hsurj
  rw [(e₁.trans e₂).toLinearEquiv.finrank_eq, Module.finrank_self]

theorem finrank_eq_one_of_isUnit (g : Fin d → MvPowerSeries (Fin d) k)
    (hg : ∀ i, constantCoeff (g i) = 0) (hu : IsUnit (MvFormalGroup.linearPart g))
    [Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g))] :
    Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g)) = 1 := by
  rw [(Ideal.quotientEquivAlgOfEq k (span_eq_mX g hg hu)).toLinearEquiv.finrank_eq,
    finrank_quotient_mX]

theorem isUnit_of_rank_eq (L : Matrix (Fin d) (Fin d) k) (hL : L.rank = d) : IsUnit L := by
  classical
  rw [← Matrix.mulVec_surjective_iff_isUnit]
  have htop : LinearMap.range L.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact hL
  intro v
  obtain ⟨w, hw⟩ := LinearMap.range_eq_top.1 htop v
  exact ⟨w, by rw [← Matrix.mulVecLin_apply]; exact hw⟩

variable {p : ℕ} [hp : Fact p.Prime] [CharP k p]

theorem exists_finrank_eq_pow_aux (n : ℕ) :
    ∀ (Ψ Φ : MvFormalGroup d k) [Ψ.IsComm] [Φ.IsComm] (ψ : Ψ.Hom Φ),
      Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries)) →
      Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries)) = n →
      ∃ h : ℕ, n = p ^ h := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Ψ Φ _ _ ψ hfin hn
    haveI := hfin
    set r := (MvFormalGroup.linearPart ψ.toPowerSeries).rank with hr
    have hrd : r ≤ d := Matrix.rank_le_width _
    by_cases hfull : r = d
    ·
      refine ⟨0, ?_⟩
      rw [pow_zero, ← hn]
      exact finrank_eq_one_of_isUnit ψ.toPowerSeries ψ.constantCoeff_eq_zero
        (isUnit_of_rank_eq _ hfull)
    ·
      obtain ⟨Ψ', hc', π, ρ, ψ', -, -, -, -, -, hfin', hmul⟩ :=
        MvFormalGroup.Hom.exists_comp_eq_and_comp_eq_X_pow_and_finrank_eq_pow_mul p Ψ Φ ψ hfin
      haveI := hc'
      haveI := hfin'
      set n' := Module.finrank k
        (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ'.toPowerSeries)) with hn'
      rw [hn] at hmul

      have hJ : Ideal.span (Set.range ψ.toPowerSeries) ≠ ⊤ :=
        fun h => mX_ne_top (top_le_iff.1 (h ▸ span_le_mX ψ.toPowerSeries ψ.constantCoeff_eq_zero))
      haveI : Nontrivial (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries)) :=
        Ideal.Quotient.nontrivial_iff.2 hJ
      have hnpos : 0 < n := hn ▸ Module.finrank_pos
      have hdr : 1 ≤ d - r := by omega
      have hp2 : 2 ≤ p ^ (d - r) :=
        le_trans hp.out.two_le (le_self_pow₀ hp.out.one_lt.le (by omega))
      have hn'pos : 0 < n' := by
        rcases Nat.eq_zero_or_pos n' with h0 | h0
        · rw [h0, mul_zero] at hmul; omega
        · exact h0
      have hlt : n' < n := by
        calc n' < 2 * n' := by omega
          _ ≤ p ^ (d - r) * n' := Nat.mul_le_mul_right _ hp2
          _ = n := hmul.symm
      obtain ⟨h', hh'⟩ := ih n' hlt Ψ' Φ ψ' hfin' rfl
      exact ⟨d - r + h', by rw [pow_add, ← hh', hmul]⟩

omit hp [CharP k p] in
theorem finrank_map_eq {ι : Type*} (g : ι → MvPowerSeries (Fin d) k) (N : ℕ)
    (hN : mX k d ^ N ≤ Ideal.span (Set.range g))
    (κ : Type u) [Field κ] (f : k →+* κ) :
    Module.finrank κ (MvPowerSeries (Fin d) κ ⧸
        Ideal.span (Set.range fun i => MvPowerSeries.map f (g i))) =
      Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g)) := by
  letI : Algebra k κ := f.toAlgebra
  obtain ⟨e, -⟩ :=
    MvPowerSeries.exists_algEquiv_tensorProduct_quotient_span_map_of_pow_span_X_le κ g N hN
  have hf : algebraMap k κ = f := RingHom.algebraMap_toAlgebra f
  rw [hf] at e
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_baseChange]

theorem main (Φ Φ' : MvFormalGroup d k) [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ')
    (hfin : Module.Finite k
      (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range φ.toPowerSeries))) :
    ∃ h : ℕ, ∀ (κ : Type u) [Field κ] (f : k →+* κ),
      Module.finrank κ (MvPowerSeries (Fin d) κ ⧸
        Ideal.span (Set.range fun i => MvPowerSeries.map f (φ.toPowerSeries i))) = p ^ h := by
  haveI := hfin
  obtain ⟨h, hh⟩ := exists_finrank_eq_pow_aux (p := p) _ Φ Φ' φ hfin rfl
  obtain ⟨N, hN⟩ := exists_pow_mX_le (Ideal.span (Set.range φ.toPowerSeries))
  exact ⟨h, fun κ _ f => by rw [finrank_map_eq φ.toPowerSeries N hN κ f, hh]⟩

end P2mKcKernelOrder

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] {d : ℕ}
    (Φ Φ' : MvFormalGroup d k) [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ')
    (hfin : Module.Finite k
      (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range φ.toPowerSeries))) :
    ∃ h : ℕ, ∀ (κ : Type u) [Field κ] (f : k →+* κ),
      Module.finrank κ (MvPowerSeries (Fin d) κ ⧸
        Ideal.span (Set.range fun i => MvPowerSeries.map f (φ.toPowerSeries i))) = p ^ h :=
  P2mKcKernelOrder.main Φ Φ' φ hfin

end

end S_MvFormalGroup_Hom_exists_finrank_quotient_span_range_map_eq_prime_pow_of_isComm
end P2MW
export P2MW.S_MvFormalGroup_Hom_exists_finrank_quotient_span_range_map_eq_prime_pow_of_isComm (solution)
