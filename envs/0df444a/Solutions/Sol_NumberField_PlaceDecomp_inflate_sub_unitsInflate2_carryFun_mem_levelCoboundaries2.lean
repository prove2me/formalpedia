-- Prove2me | solution 1 for NumberField.PlaceDecomp.inflate_sub_unitsInflate2_carryFun_mem_levelCoboundaries2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/6cb6f720-3e8c-5991-b80e-2b4a88519808

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_LocalInvariant
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import Theorems.Thm_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion
import Theorems.Thm_NumberField_PlaceDecomp_mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv
import Theorems.Thm_IntermediateField_apply_algebraMap_eq_and_norm_apply_eq_of_ringEquiv_of_padic
import Theorems.Thm_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass
import Theorems.Thm_ExtCitation_LocalLevel_isSolvable_of_faithfulSMul_of_padic
import Theorems.Thm_ExtCitation_LocalLevel_finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq
import Theorems.Thm_ExtCitation_LocalLevel_map_eq_natCard_smul_of_isLocalFundamentalClass
import Theorems.Thm_ExtCitation_LocalLevel_isLocalFundamentalClass_of_pin
import Theorems.Thm_PadicAlgCl_finrank_adjoin_rootsOfUnity_eq_and_forall_norm_eq_zpow
import Theorems.Thm_PadicAlgCl_exists_apply_eq_pow_pow_of_pow_eq_one_of_not_dvd
import Theorems.Thm_PadicAlgCl_exists_algEquiv_apply_eq_pow_of_pow_eq_one
import Theorems.Thm_groupCohomology_infNatTrans_app_H2pi_carryFun_eq_card_nsmul
import Theorems.Thm_ExtCitation_LocalLevel_isZero_groupCohomology_one_res_units
import Theorems.Thm_groupCohomology_carryFun_mem_cocycles2
import Theorems.Thm_ExtCitation_LocalLevel_exists_ramification_inertia_Rw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_inflate_sub_unitsInflate2_carryFun_mem_levelCoboundaries2
p2m_attr_erase "instance" "ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
open CategoryTheory groupCohomology NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp

namespace F2a

noncomputable abbrev L0 (q : Nat.Primes) [Fact ((q : ℕ)).Prime] (p : ℕ) : IntermediateField ℚ_[q] (PadicAlgCl q) :=
  IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}

section ed_helpers

universe u

theorem ed_map_congr {k : Type u} [CommRing k] {G H : Type u} [Group G] [Group H] {A : Rep k H} {B : Rep k G}
    (f₁ f₂ : G →* H) (hf : f₁ = f₂) (φ₁ : Rep.res f₁ A ⟶ B) (n : ℕ) :
    ∃ φ₂ : Rep.res f₂ A ⟶ B, (∀ x, φ₂.hom x = φ₁.hom x) ∧ groupCohomology.map f₁ φ₁ n = groupCohomology.map f₂ φ₂ n := by
  subst hf
  exact ⟨φ₁, fun _ => rfl, rfl⟩

theorem ed_layer (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L] [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (v : (↥L)ˣ), ((g • v : (↥L)ˣ) : L) = g • (v : L))
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction G (↥L)ˣ))
    (hu : ExtCitation.LocalLevel.IsLocalFundamentalClass q L G ⊥ u)
    (M : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] M] [IsGalois ℚ_[q] M] (hLM : L ≤ M)
    (uM : groupCohomology.H2 (Rep.ofAlgebraAutOnUnits ℚ_[q] M))
    (huM : ExtCitation.LocalLevel.IsLocalFundamentalClass q M (M ≃ₐ[ℚ_[q]] M) ⊥ uM)
    (r : (M ≃ₐ[ℚ_[q]] M) →* G) (hrs : Function.Surjective r)
    (hr : ∀ (h : M ≃ₐ[ℚ_[q]] M) (x : L), ((r h • x : L) : PadicAlgCl q) = ((h ⟨(x : PadicAlgCl q), hLM x.2⟩ : M) : PadicAlgCl q))
    (ι : Rep.res r (Rep.ofMulDistribMulAction G (↥L)ˣ) ⟶ Rep.ofAlgebraAutOnUnits ℚ_[q] M)
    (hι : ∀ v : (↥L)ˣ, (((Additive.toMul (ι.hom (Additive.ofMul v)) : (↥M)ˣ) : M) : PadicAlgCl q) = ((v : L) : PadicAlgCl q)) :
    (groupCohomology.map r ι 2).hom u = Nat.card ↥r.ker • uM := by

  have hH : ∀ (h : M ≃ₐ[ℚ_[q]] M) (x : ℚ_[q]), h • algebraMap ℚ_[q] M x = algebraMap ℚ_[q] M x := fun h x => h.commutes x
  have hHc : ∀ (h : M ≃ₐ[ℚ_[q]] M) (v : (↥M)ˣ), ((h • v : (↥M)ˣ) : M) = h • (v : M) := fun h v => rfl
  have hsolv : Group.IsSolvable (M ≃ₐ[ℚ_[q]] M) := ExtCitation.LocalLevel.isSolvable_of_faithfulSMul_of_padic q M _ hH
  have hbaseM : ExtCitation.LocalLevel.IsBase q M (M ≃ₐ[ℚ_[q]] M) ⊥ := by
    refine ⟨bot_le, fun x => ?_⟩
    rw [IntermediateField.mem_bot]
    constructor
    · rintro ⟨y, hy⟩ g
      have hx : x = algebraMap ℚ_[q] M y := Subtype.ext (by rw [← hy]; rfl)
      rw [hx]
      exact g.commutes y
    · intro hfix
      have hx : x ∈ (⊥ : IntermediateField ℚ_[q] M) := (IsGalois.mem_bot_iff_fixed x).mpr hfix
      rw [IntermediateField.mem_bot] at hx
      obtain ⟨y, hy⟩ := hx
      exact ⟨y, by rw [← hy]; rfl⟩

  let e : G ≃* (M ≃ₐ[ℚ_[q]] M) ⧸ r.ker := (QuotientGroup.quotientKerEquivOfSurjective r hrs).symm
  have hre : r = e.symm.toMonoidHom.comp (QuotientGroup.mk' r.ker) := by
    ext h
    show r h = QuotientGroup.quotientKerEquivOfSurjective r hrs (QuotientGroup.mk h)
    exact (QuotientGroup.kerLift_mk r h).symm
  obtain ⟨ι', hι', hmap⟩ := ed_map_congr r _ hre ι 2

  have hker : ∀ h : M ≃ₐ[ℚ_[q]] M, h ∈ r.ker ↔ ∀ x : L, ((h ⟨(x : PadicAlgCl q), hLM x.2⟩ : M) : PadicAlgCl q) = (x : PadicAlgCl q) := by
    intro h
    rw [MonoidHom.mem_ker]
    constructor
    · intro h1 x
      rw [← hr, h1, one_smul]
    · intro hx
      apply FaithfulSMul.eq_of_smul_eq_smul (α := ↥L)
      intro x
      apply Subtype.ext
      show ((r h • x : L) : PadicAlgCl q) = ((1 : G) • x : L)
      rw [one_smul, hr, hx]
  have hL : ∀ x : M, (x : PadicAlgCl q) ∈ L ↔ ∀ n ∈ r.ker, n • x = x := by
    intro x
    constructor
    · intro hx n hn
      have := (hker n).mp hn ⟨x, hx⟩
      apply Subtype.ext
      show ((n x : M) : PadicAlgCl q) = x
      convert this using 2
    · intro hfix

      let E : IntermediateField ℚ_[q] M := (IntermediateField.inclusion hLM).fieldRange
      have hEle : E.fixingSubgroup ≤ r.ker := by
        intro h hh
        rw [hker]
        intro y
        have := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hh (IntermediateField.inclusion hLM y) ⟨y, rfl⟩
        exact congrArg (fun z : M => (z : PadicAlgCl q)) this
      have hxE : x ∈ IntermediateField.fixedField E.fixingSubgroup := by
        rw [IntermediateField.mem_fixedField_iff]
        intro h hh
        exact hfix h (hEle hh)
      rw [IsGalois.fixedField_fixingSubgroup] at hxE
      obtain ⟨y, hy⟩ := hxE
      rw [← hy]
      exact y.2
  have he : ∀ (g : G) (h : M ≃ₐ[ℚ_[q]] M), (QuotientGroup.mk h : (M ≃ₐ[ℚ_[q]] M) ⧸ r.ker) = e g →
      ∀ x : L, ((g • x : L) : PadicAlgCl q) = ((h • (⟨(x : PadicAlgCl q), hLM x.2⟩ : M) : M) : PadicAlgCl q) := by
    intro g h hgh x
    have hg : g = r h := by
      have := congrArg e.symm hgh
      rw [MulEquiv.symm_apply_apply] at this
      rw [← this]
      exact QuotientGroup.kerLift_mk r h
    rw [hg, hr]
    rfl
  have hι'' : ∀ v : (↥L)ˣ, (((Additive.toMul (ι'.hom (Additive.ofMul v)) : (↥M)ˣ) : M) : PadicAlgCl q) = ((v : L) : PadicAlgCl q) := by
    intro v; rw [hι']; exact hι v
  have key := ExtCitation.LocalLevel.map_eq_natCard_smul_of_isLocalFundamentalClass q M (M ≃ₐ[ℚ_[q]] M) hH hHc hsolv
    ⊥ hbaseM L hLM G hcompat r.ker e hL he u hu uM huM ι' hι''
  rw [hmap]
  exact key

end ed_helpers

theorem eb_norm_pow_sub_pow_le {K : Type*} [NormedField K] [IsUltrametricDist K]
    (a b : K) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) : ‖a ^ n - b ^ n‖ ≤ ‖a - b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
    rw [hsplit]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖a‖ * ‖a ^ n - b ^ n‖ ≤ 1 * ‖a - b‖ := mul_le_mul ha ih (norm_nonneg _) zero_le_one
        _ = ‖a - b‖ := one_mul _
    · rw [norm_mul, norm_pow]
      calc ‖a - b‖ * ‖b‖ ^ n ≤ ‖a - b‖ * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hb) (norm_nonneg _)
        _ = ‖a - b‖ := mul_one _

theorem eb_carryFun_zsmul {G : Type} [Group G] (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    {A : Rep ℤ G} (m : ℤ) (a : A) : carryFun s hs hfin (m • a) = m • carryFun s hs hfin a := by
  funext p
  simp only [carryFun, Pi.smul_apply]
  split_ifs <;> simp

theorem eb_H2π_carryFun_ofMul_zpow (q : Nat.Primes) [Fact ((q : ℕ)).Prime] (p : ℕ)
    (φ : (L0 q p) ≃ₐ[ℚ_[q]] (L0 q p)) (hs : ∀ σ, σ ∈ Subgroup.zpowers φ) (hfin : IsOfFinOrder φ)
    (π₀ : (↥(L0 q p))ˣ) (m : ℤ)
    (hc : carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p)) (Additive.ofMul π₀) ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p)))
    (hcm : carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p)) (Additive.ofMul (π₀ ^ m)) ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p))) :
    (H2π (Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p))).hom ⟨carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p)) (Additive.ofMul (π₀ ^ m)), hcm⟩ =
      m • (H2π (Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p))).hom ⟨carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p)) (Additive.ofMul π₀), hc⟩ := by
  rw [← map_zsmul]
  congr 1
  apply Subtype.ext
  change carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p)) (Additive.ofMul (π₀ ^ m)) =
    m • carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p)) (Additive.ofMul π₀)
  rw [← eb_carryFun_zsmul]
  rfl

theorem eb_card_ker_eq {H G G₀ : Type} [Group H] [Group G] [Group G₀] [Finite H] [Finite G] [Finite G₀]
    (r₂ : H →* G) (h₂ : Function.Surjective r₂) (r₀ : H →* G₀) (h₀ : Function.Surjective r₀)
    (p : ℕ) (hp : 0 < p) (hG₀ : Nat.card G₀ = p) (hpn : p ∣ Nat.card G) :
    Nat.card ↥r₀.ker = (Nat.card G / p) * Nat.card ↥r₂.ker := by
  have e₂ : Nat.card H = Nat.card G * Nat.card ↥r₂.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup r₂.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective r₂ h₂).toEquiv]
  have e₀ : Nat.card H = Nat.card G₀ * Nat.card ↥r₀.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup r₀.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective r₀ h₀).toEquiv]
  obtain ⟨d, hd⟩ := hpn
  rw [hd, Nat.mul_div_cancel_left d hp]
  have : p * Nat.card ↥r₀.ker = p * (d * Nat.card ↥r₂.ker) := by
    rw [← hG₀, ← e₀, e₂, hG₀, hd, mul_assoc]
  exact Nat.eq_of_mul_eq_mul_left hp this

section ed_trivial

theorem ed_isLocalFundamentalClass_L0 (q : Nat.Primes) [Fact ((q : ℕ)).Prime] (p : ℕ) [Fact p.Prime]
    [FiniteDimensional ℚ_[q] (L0 q p)] [IsGalois ℚ_[q] (L0 q p)]
    (φ : (L0 q p) ≃ₐ[ℚ_[q]] (L0 q p)) (hs : ∀ σ, σ ∈ Subgroup.zpowers φ) (hfin : IsOfFinOrder φ)
    (hφ : ∀ x : L0 q p, (x : PadicAlgCl q) ^ ((q : ℕ) ^ p - 1) = 1 → (φ x : PadicAlgCl q) = (x : PadicAlgCl q) ^ (q : ℕ))
    (π₀ : (↥(L0 q p))ˣ) (hπ₀ : ((π₀ : L0 q p) : PadicAlgCl q) = algebraMap ℚ_[q] (PadicAlgCl q) (q : ℚ_[q]))
    (hcπ : carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p)) (Additive.ofMul π₀) ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p))) :
    ExtCitation.LocalLevel.IsLocalFundamentalClass q (L0 q p) ((L0 q p) ≃ₐ[ℚ_[q]] (L0 q p)) ⊥
      ((H2π (Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p))).hom ⟨carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p)) (Additive.ofMul π₀), hcπ⟩) := by
  have hq : ((q : ℕ)).Prime := Fact.out
  have hp : p.Prime := Fact.out

  have hG₀ : ∀ (g : (L0 q p) ≃ₐ[ℚ_[q]] (L0 q p)) (x : ℚ_[q]), g • algebraMap ℚ_[q] (L0 q p) x = algebraMap ℚ_[q] (L0 q p) x :=
    fun g x => g.commutes x
  have hc₀ : ∀ (g : (L0 q p) ≃ₐ[ℚ_[q]] (L0 q p)) (v : (↥(L0 q p))ˣ), ((g • v : (↥(L0 q p))ˣ) : L0 q p) = g • (v : L0 q p) := fun g v => rfl
  have hbase : ExtCitation.LocalLevel.IsBase q (L0 q p) ((L0 q p) ≃ₐ[ℚ_[q]] (L0 q p)) ⊥ := by
    refine ⟨bot_le, fun x => ?_⟩
    rw [IntermediateField.mem_bot]
    constructor
    · rintro ⟨y, hy⟩ g
      have hx : x = algebraMap ℚ_[q] (L0 q p) y := Subtype.ext (by rw [← hy]; rfl)
      rw [hx]
      exact g.commutes y
    · intro hfix
      have hx : x ∈ (⊥ : IntermediateField ℚ_[q] (L0 q p)) := (IsGalois.mem_bot_iff_fixed x).mpr hfix
      rw [IntermediateField.mem_bot] at hx
      obtain ⟨y, hy⟩ := hx
      exact ⟨y, by rw [← hy]; rfl⟩

  have hres : Nat.card (IsLocalRing.ResidueField (ExtCitation.LocalLevel.Rw q (⊥ : IntermediateField ℚ_[q] (PadicAlgCl q)))) = q := by
    obtain ⟨e, f, he, hf, -, hcard, hef⟩ := ExtCitation.LocalLevel.exists_ramification_inertia_Rw q (⊥ : IntermediateField ℚ_[q] (PadicAlgCl q))
    rw [IntermediateField.finrank_bot] at hef
    have hf1 : f = 1 := by
      rcases Nat.eq_one_of_mul_eq_one_left hef with h | h <;> first | exact h | omega
    rw [hcard, hf1, pow_one]

  obtain ⟨-, -, hval, hteich⟩ := PadicAlgCl.finrank_adjoin_rootsOfUnity_eq_and_forall_norm_eq_zpow (q : ℕ) p hp.pos
  have hnormq : ‖((q : ℕ) : PadicAlgCl q)‖ = (q : ℝ)⁻¹ := by
    rw [show ((q : ℕ) : PadicAlgCl q) = ((q : ℕ) : ℚ_[q]) from by push_cast; rfl, PadicAlgCl.norm_extends, Padic.norm_p]
  have hπ₀' : ((π₀ : L0 q p) : PadicAlgCl q) = ((q : ℕ) : PadicAlgCl q) := by rw [hπ₀, map_natCast]
  have hsubmax : ∀ a b : PadicAlgCl q, ‖a - b‖ ≤ max ‖a‖ ‖b‖ := fun a b => by
    simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max a (-b)

  have hiso : ∀ x : L0 q p, ‖((φ x : L0 q p) : PadicAlgCl q)‖ = ‖(x : PadicAlgCl q)‖ :=
    (IntermediateField.apply_algebraMap_eq_and_norm_apply_eq_of_ringEquiv_of_padic q (L0 q p) (L0 q p) φ.toRingEquiv).2

  have d : ExtCitation.LocalLevel.IsUnramOverlayerDatum q (L0 q p) ((L0 q p) ≃ₐ[ℚ_[q]] (L0 q p)) ⊥ (L0 q p) le_rfl
      ((L0 q p) ≃ₐ[ℚ_[q]] (L0 q p)) ⊥ ⊥ (QuotientGroup.quotientBot).symm φ π₀ := by
    refine ⟨hG₀, hc₀, hbase.mem_iff, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    ·
      intro x
      exact ⟨fun _ h hh => by rw [Subgroup.mem_bot.mp hh, one_smul], fun _ => x.2⟩
    ·
      intro g h hgh x
      have : g = h := by
        have := congrArg QuotientGroup.quotientBot hgh
        first | exact this.symm | simpa using this.symm | simpa +zetaDelta using this.symm
      subst this
      rfl
    ·
      exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
    ·
      intro h
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective h
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hs g)
      exact ⟨k, (map_zpow (QuotientGroup.mk' (⊥ : Subgroup ((L0 q p) ≃ₐ[ℚ_[q]] (L0 q p)))) φ k).symm⟩
    ·
      intro x _ hx1
      rw [hres]
      show ‖((φ x : L0 q p) : PadicAlgCl q) - (x : PadicAlgCl q) ^ (q : ℕ)‖ < 1
      rcases hx1.lt_or_eq with hlt | heq
      ·
        refine lt_of_le_of_lt (hsubmax _ _) (max_lt ?_ ?_)
        · rwa [hiso]
        · rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hlt hq.ne_zero
      ·
        obtain ⟨ζ', hζ', hxζ⟩ := hteich (x : PadicAlgCl q) x.2 heq
        have hζ'mem : ζ' ∈ L0 q p := IntermediateField.subset_adjoin _ _ hζ'
        have hφζ : ((φ ⟨ζ', hζ'mem⟩ : L0 q p) : PadicAlgCl q) = ζ' ^ (q : ℕ) := hφ ⟨ζ', hζ'mem⟩ hζ'
        have h1 : ‖((φ x : L0 q p) : PadicAlgCl q) - ζ' ^ (q : ℕ)‖ < 1 := by
          rw [← hφζ]
          have : ((φ x : L0 q p) : PadicAlgCl q) - ((φ ⟨ζ', hζ'mem⟩ : L0 q p) : PadicAlgCl q) =
              ((φ (x - ⟨ζ', hζ'mem⟩) : L0 q p) : PadicAlgCl q) := by
            rw [map_sub]; rfl
          rw [this, hiso]
          exact hxζ
        have h2 : ‖ζ' ^ (q : ℕ) - (x : PadicAlgCl q) ^ (q : ℕ)‖ < 1 := by
          have hζ'1 : ‖ζ'‖ ≤ 1 := by
            have := norm_pow ζ' ((q : ℕ) ^ p - 1)
            rw [hζ', norm_one] at this
            by_contra hgt
            rw [not_le] at hgt
            have hpos : 0 < (q : ℕ) ^ p - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hp.ne_zero hq.one_lt)
            exact absurd this.symm (ne_of_gt (one_lt_pow₀ hgt hpos.ne'))

          calc ‖ζ' ^ (q : ℕ) - (x : PadicAlgCl q) ^ (q : ℕ)‖ ≤ ‖ζ' - (x : PadicAlgCl q)‖ :=
                eb_norm_pow_sub_pow_le ζ' (x : PadicAlgCl q) hζ'1 heq.le (q : ℕ)
            _ = ‖(x : PadicAlgCl q) - ζ'‖ := norm_sub_rev _ _
            _ < 1 := hxζ
        calc ‖((φ x : L0 q p) : PadicAlgCl q) - (x : PadicAlgCl q) ^ (q : ℕ)‖
            = ‖(((φ x : L0 q p) : PadicAlgCl q) - ζ' ^ (q : ℕ)) + (ζ' ^ (q : ℕ) - (x : PadicAlgCl q) ^ (q : ℕ))‖ := by ring_nf
          _ ≤ max ‖((φ x : L0 q p) : PadicAlgCl q) - ζ' ^ (q : ℕ)‖ ‖ζ' ^ (q : ℕ) - (x : PadicAlgCl q) ^ (q : ℕ)‖ :=
              IsUltrametricDist.norm_add_le_max _ _
          _ < 1 := max_lt h1 h2
    ·
      intro h
      apply Units.ext
      apply Subtype.ext
      show ((h (π₀ : L0 q p) : L0 q p) : PadicAlgCl q) = ((π₀ : L0 q p) : PadicAlgCl q)
      have : (π₀ : L0 q p) = algebraMap ℚ_[q] (L0 q p) (q : ℚ_[q]) := Subtype.ext (by rw [hπ₀]; rfl)
      rw [this, AlgEquiv.commutes]
    ·
      rw [hπ₀]; exact ⟨(q : ℚ_[q]), rfl⟩
    ·
      rw [hπ₀', hnormq]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hq.one_lt)
    ·
      intro y _ hy
      rw [hπ₀', hnormq]
      rcases eq_or_ne (y : PadicAlgCl q) 0 with h0 | h0
      · rw [h0, norm_zero]; positivity
      · obtain ⟨k, hk⟩ := hval (y : PadicAlgCl q) y.2 h0
        rw [hk] at hy ⊢
        have hk0 : k < 0 := by
          by_contra hk'
          rw [not_lt] at hk'
          exact absurd hy (not_lt.mpr (one_le_zpow₀ (by exact_mod_cast hq.one_lt.le) hk'))
        calc ((q : ℕ) : ℝ) ^ k ≤ ((q : ℕ) : ℝ) ^ (-1 : ℤ) := zpow_le_zpow_right₀ (by exact_mod_cast hq.one_lt.le) (by omega)
          _ = (q : ℝ)⁻¹ := by rw [zpow_neg_one]

  refine ExtCitation.LocalLevel.isLocalFundamentalClass_of_pin q (L0 q p) ((L0 q p) ≃ₐ[ℚ_[q]] (L0 q p)) hG₀ hc₀ ⊥ hbase d _ ?_
  intro ι hι hfin' hc'

  have hrhs := groupCohomology.infNatTrans_app_H2pi_carryFun_eq_card_nsmul φ hs hfin (⊥ : Subgroup ((L0 q p) ≃ₐ[ℚ_[q]] (L0 q p)))
    d.mem_zpowers hfin' (A := Rep.ofMulDistribMulAction ((L0 q p) ≃ₐ[ℚ_[q]] (L0 q p)) (↥(L0 q p))ˣ) d.piInv hcπ hc'
  erw [hrhs, Subgroup.card_bot, one_smul]

  have hid : (QuotientGroup.quotientBot.symm : ((L0 q p) ≃ₐ[ℚ_[q]] (L0 q p)) ≃* ((L0 q p) ≃ₐ[ℚ_[q]] (L0 q p)) ⧸ (⊥ : Subgroup _)).symm.toMonoidHom.comp
      (QuotientGroup.mk' (⊥ : Subgroup ((L0 q p) ≃ₐ[ℚ_[q]] (L0 q p)))) = MonoidHom.id _ := by
    ext g
    rfl
  obtain ⟨ι', hι', hmap⟩ := ed_map_congr _ _ hid ι 2
  rw [hmap]
  have hι'id : ι' = 𝟙 (Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p)) := by
    ext v
    show ι'.hom v = v
    rw [hι']
    apply Additive.toMul.injective
    apply Units.ext
    apply Subtype.ext
    exact hι (Additive.toMul v)
  rw [hι'id]
  erw [groupCohomology.map_id]
  rfl

end ed_trivial

theorem stageB (q : Nat.Primes) [Fact ((q : ℕ)).Prime] (p : ℕ) [Fact p.Prime]
    (L₂ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L₂]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L₂] [FaithfulSMul G L₂] [MulDistribMulAction G (↥L₂)ˣ]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L₂ x = algebraMap ℚ_[q] L₂ x)
    (hcompat : ∀ (g : G) (v : (↥L₂)ˣ), ((g • v : (↥L₂)ˣ) : L₂) = g • (v : L₂))
    (hbase : ExtCitation.LocalLevel.IsBase q L₂ G ⊥)
    (u₂ : groupCohomology.H2 (Rep.ofMulDistribMulAction G (↥L₂)ˣ))
    (hu₂ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L₂ G ⊥ u₂)
    (hpn : p ∣ Nat.card G) (m : ℤ)
    (φ : (L0 q p) ≃ₐ[ℚ_[q]] (L0 q p)) (hs : ∀ σ, σ ∈ Subgroup.zpowers φ) (hfin : IsOfFinOrder φ)
    (hφ : ∀ x : L0 q p, (x : PadicAlgCl q) ^ ((q : ℕ) ^ p - 1) = 1 → (φ x : PadicAlgCl q) = (x : PadicAlgCl q) ^ (q : ℕ))
    (α : (↥(L0 q p))ˣ) (hα : ((α : L0 q p) : PadicAlgCl q) = algebraMap ℚ_[q] (PadicAlgCl q) ((q : ℚ_[q]) ^ m))
    (hc : carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p)) (Additive.ofMul α) ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p)))

    (M : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] M] [IsGalois ℚ_[q] M]
    (hL₂M : L₂ ≤ M) (hL₀M : L0 q p ≤ M)
    (r₂ : (M ≃ₐ[ℚ_[q]] M) →* G) (hr₂s : Function.Surjective r₂)
    (hr₂ : ∀ (h : M ≃ₐ[ℚ_[q]] M) (x : L₂), ((r₂ h • x : L₂) : PadicAlgCl q) = ((h ⟨(x : PadicAlgCl q), hL₂M x.2⟩ : M) : PadicAlgCl q))
    (ι₂ : Rep.res r₂ (Rep.ofMulDistribMulAction G (↥L₂)ˣ) ⟶ Rep.ofAlgebraAutOnUnits ℚ_[q] M)
    (hι₂ : ∀ v : (↥L₂)ˣ, (((Additive.toMul (ι₂.hom (Additive.ofMul v)) : (↥M)ˣ) : M) : PadicAlgCl q) = ((v : L₂) : PadicAlgCl q))
    (r₀ : (M ≃ₐ[ℚ_[q]] M) →* ((L0 q p) ≃ₐ[ℚ_[q]] (L0 q p))) (hr₀s : Function.Surjective r₀)
    (hr₀ : ∀ (h : M ≃ₐ[ℚ_[q]] M) (x : L0 q p), ((r₀ h x : L0 q p) : PadicAlgCl q) = ((h ⟨(x : PadicAlgCl q), hL₀M x.2⟩ : M) : PadicAlgCl q))
    (ι₀ : Rep.res r₀ (Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p)) ⟶ Rep.ofAlgebraAutOnUnits ℚ_[q] M)
    (hι₀ : ∀ v : (↥(L0 q p))ˣ, (((Additive.toMul (ι₀.hom (Additive.ofMul v)) : (↥M)ˣ) : M) : PadicAlgCl q) = ((v : L0 q p) : PadicAlgCl q)) :
    (groupCohomology.map r₂ ι₂ 2).hom (m • ((Nat.card G / p) • u₂)) =
      (groupCohomology.map r₀ ι₀ 2).hom ((H2π (Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p))).hom
        ⟨carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p)) (Additive.ofMul α), hc⟩) := by
  have hq : ((q : ℕ)).Prime := Fact.out
  have hp : p.Prime := Fact.out

  obtain ⟨hgal₀, hfr₀, -, -⟩ := PadicAlgCl.finrank_adjoin_rootsOfUnity_eq_and_forall_norm_eq_zpow (q : ℕ) p hp.pos
  haveI : IsGalois ℚ_[q] (L0 q p) := hgal₀
  haveI : FiniteDimensional ℚ_[q] (L0 q p) := Module.finite_of_finrank_pos (by rw [hfr₀]; exact hp.pos)

  have hH : ∀ (h : M ≃ₐ[ℚ_[q]] M) (x : ℚ_[q]), h • algebraMap ℚ_[q] M x = algebraMap ℚ_[q] M x := fun h x => h.commutes x
  have hHc : ∀ (h : M ≃ₐ[ℚ_[q]] M) (v : (↥M)ˣ), ((h • v : (↥M)ˣ) : M) = h • (v : M) := fun h v => rfl
  have hsolv : Group.IsSolvable (M ≃ₐ[ℚ_[q]] M) := ExtCitation.LocalLevel.isSolvable_of_faithfulSMul_of_padic q M _ hH
  have hbaseM : ExtCitation.LocalLevel.IsBase q M (M ≃ₐ[ℚ_[q]] M) ⊥ := by
    refine ⟨bot_le, fun x => ?_⟩
    rw [IntermediateField.mem_bot]
    constructor
    · rintro ⟨y, hy⟩ g
      have hx : x = algebraMap ℚ_[q] M y := Subtype.ext (by rw [← hy]; rfl)
      rw [hx]
      exact g.commutes y
    · intro hfix
      have hx : x ∈ (⊥ : IntermediateField ℚ_[q] M) := (IsGalois.mem_bot_iff_fixed x).mpr hfix
      rw [IntermediateField.mem_bot] at hx
      obtain ⟨y, hy⟩ := hx
      exact ⟨y, by rw [← hy]; rfl⟩
  obtain ⟨uM, huM, -⟩ := ExtCitation.LocalLevel.existsUnique_isLocalFundamentalClass q M (M ≃ₐ[ℚ_[q]] M) hH hHc hsolv ⊥ hbaseM

  have key₂ := ed_layer q L₂ G hcompat u₂ hu₂ M hL₂M uM huM r₂ hr₂s hr₂ ι₂ hι₂

  have hqmem : algebraMap ℚ_[q] (PadicAlgCl q) (q : ℚ_[q]) ∈ L0 q p := IntermediateField.algebraMap_mem _ _
  have hq0 : (⟨algebraMap ℚ_[q] (PadicAlgCl q) (q : ℚ_[q]), hqmem⟩ : L0 q p) ≠ 0 := by
    intro h
    have := congrArg (fun z : L0 q p => (z : PadicAlgCl q)) h
    simp only [ZeroMemClass.coe_zero, map_eq_zero] at this
    exact hq.ne_zero (by exact_mod_cast this)
  let π₀ : (↥(L0 q p))ˣ := Units.mk0 _ hq0
  have hπ₀ : ((π₀ : L0 q p) : PadicAlgCl q) = algebraMap ℚ_[q] (PadicAlgCl q) (q : ℚ_[q]) := rfl
  have hc₀ : ∀ (g : (L0 q p) ≃ₐ[ℚ_[q]] (L0 q p)) (v : (↥(L0 q p))ˣ), ((g • v : (↥(L0 q p))ˣ) : L0 q p) = g • (v : L0 q p) := fun g v => rfl
  have hφπ : (Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p)).ρ φ (Additive.ofMul π₀) = Additive.ofMul π₀ := by
    show Additive.ofMul (φ • π₀) = Additive.ofMul π₀
    congr 1
    apply Units.ext; apply Subtype.ext
    show ((φ (π₀ : L0 q p) : L0 q p) : PadicAlgCl q) = ((π₀ : L0 q p) : PadicAlgCl q)
    have : (π₀ : L0 q p) = algebraMap ℚ_[q] (L0 q p) (q : ℚ_[q]) := Subtype.ext (by rw [hπ₀]; rfl)
    rw [this, AlgEquiv.commutes]
  have hcπ := groupCohomology.carryFun_mem_cocycles2 φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p)) (Additive.ofMul π₀) hφπ
  have hu₀ := ed_isLocalFundamentalClass_L0 q p φ hs hfin hφ π₀ hπ₀ hcπ
  have key₀ := ed_layer q (L0 q p) ((L0 q p) ≃ₐ[ℚ_[q]] (L0 q p)) hc₀ _ hu₀ M hL₀M uM huM r₀ hr₀s hr₀ ι₀ hι₀

  have hα' : α = π₀ ^ m := by
    apply Units.ext
    apply (algebraMap (L0 q p) (PadicAlgCl q)).injective
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
    show ((α : L0 q p) : PadicAlgCl q) = ((π₀ : L0 q p) : PadicAlgCl q) ^ m
    rw [hα, hπ₀, map_zpow₀]
  subst hα'

  have hG₀card : Nat.card ((L0 q p) ≃ₐ[ℚ_[q]] (L0 q p)) = p := by rw [IsGalois.card_aut_eq_finrank, hfr₀]
  have e1 : (groupCohomology.map r₀ ι₀ 2).hom (m • (H2π (Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p))).hom
      ⟨carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p)) (Additive.ofMul π₀), hcπ⟩) = m • (Nat.card ↥r₀.ker • uM) := by
    rw [map_zsmul]
    congr 1
  have e2 : (groupCohomology.map r₂ ι₂ 2).hom (m • ((Nat.card G / p) • u₂)) = m • ((Nat.card G / p) • (Nat.card ↥r₂.ker • uM)) := by
    rw [map_zsmul, map_nsmul]
    congr 2
  rw [eb_H2π_carryFun_ofMul_zpow q p φ hs hfin π₀ m hcπ hc, e1, e2, eb_card_ker_eq r₂ hr₂s r₀ hr₀s p hp.pos hG₀card hpn, smul_smul]

section eb_lift

variable (q : ℕ) [Fact q.Prime]

set_option hygiene false in
local notation "Ω" => PadicAlgCl q

variable (L : IntermediateField ℚ_[q] Ω) [Normal ℚ_[q] L]

def eb_HasLevel : Prop :=
  ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
    ∀ s : (Ω ≃ₐ[ℚ_[q]] Ω), localGaloisToGlobal q s ∈ F.fixingSubgroup → AlgEquiv.restrictNormalHom L s = 1

variable {L} in

lemma isLevelConstant₁_unitsInflate₁ (hL : eb_HasLevel q L) (b : (L ≃ₐ[ℚ_[q]] L) → Additive (L)ˣ) :
    IsLevelConstant₁ (localGaloisToGlobal q) (unitsInflate₁ L b) := by
  obtain ⟨F, hF, hFfix⟩ := hL
  refine ⟨F, hF, fun g s hs => ?_⟩
  simp only [unitsInflate₁_apply, map_mul, hFfix s hs, mul_one]

variable {L} in

lemma isLevelConstant₂_unitsInflate₂ (hL : eb_HasLevel q L) (f : (L ≃ₐ[ℚ_[q]] L) × (L ≃ₐ[ℚ_[q]] L) → Additive (L)ˣ) :
    IsLevelConstant₂ (localGaloisToGlobal q) (unitsInflate₂ L f) := by
  obtain ⟨F, hF, hFfix⟩ := hL
  refine ⟨F, hF, fun g g' s s' hs hs' => ?_⟩
  simp only [unitsInflate₂_apply, map_mul, hFfix s hs, hFfix s' hs', mul_one]

lemma unitsInflate₂_d₁₂ (b : (L ≃ₐ[ℚ_[q]] L) → Additive (L)ˣ) :
    unitsInflate₂ L ((d₁₂ (Rep.ofAlgebraAutOnUnits ℚ_[q] L)).hom b)
      = (d₁₂ (Rep.ofAlgebraAutOnUnits ℚ_[q] Ω)).hom (unitsInflate₁ L b) := by
  funext στ
  obtain ⟨σ, τ⟩ := στ
  rw [d₁₂_hom_apply, unitsInflate₂_apply, d₁₂_hom_apply]
  change Additive.ofMul (Units.map (↑(algebraMap L (PadicAlgCl q))) (Additive.toMul
      ((Additive.ofMul ((AlgEquiv.restrictNormalHom L σ) • Additive.toMul (b (AlgEquiv.restrictNormalHom L τ))) -
          b (AlgEquiv.restrictNormalHom L σ * AlgEquiv.restrictNormalHom L τ) +
          b (AlgEquiv.restrictNormalHom L σ) : Additive (L)ˣ)))) =
      (Additive.ofMul (σ • Additive.toMul (unitsInflate₁ L b τ)) - unitsInflate₁ L b (σ * τ) +
        unitsInflate₁ L b σ : Additive (PadicAlgCl q)ˣ)
  simp only [map_mul, toMul_sub, toMul_add, toMul_ofMul, ofMul_mul, unitsInflate₁_apply,
    div_eq_mul_inv, map_inv, ofMul_inv, RingHom.toMonoidHom_eq_coe]
  congr 3
  apply Units.ext
  rw [Units.coe_map, AlgEquiv.smul_units_def, AlgEquiv.smul_units_def, Units.coe_map, Units.coe_map,
    Units.coe_map]
  exact AlgEquiv.restrictNormal_commutes σ L _

variable {L} in

lemma unitsInflate₂_mem_levelCoboundaries₂_of_mem_coboundaries₂ (hL : eb_HasLevel q L)
    {c : (L ≃ₐ[ℚ_[q]] L) × (L ≃ₐ[ℚ_[q]] L) → Additive (L)ˣ}
    (hc : c ∈ coboundaries₂ (Rep.ofAlgebraAutOnUnits ℚ_[q] L)) :
    unitsInflate₂ L c ∈ levelCoboundaries₂ (localGaloisToGlobal q) (Rep.ofAlgebraAutOnUnits ℚ_[q] Ω) := by
  obtain ⟨b, rfl⟩ := hc
  exact (mem_levelCoboundaries₂_iff _ _ _).mpr
    ⟨unitsInflate₁ L b, isLevelConstant₁_unitsInflate₁ q hL b, (unitsInflate₂_d₁₂ q L b).symm⟩

variable {L} in

lemma eb_unitsInflate₂_sub_mem_levelCoboundaries₂_of_H2π_eq (hL : eb_HasLevel q L)
    (c c' : cocycles₂ (Rep.ofAlgebraAutOnUnits ℚ_[q] L))
    (h : H2π (Rep.ofAlgebraAutOnUnits ℚ_[q] L) c = H2π (Rep.ofAlgebraAutOnUnits ℚ_[q] L) c') :
    unitsInflate₂ L c - unitsInflate₂ L c' ∈ levelCoboundaries₂ (localGaloisToGlobal q) (Rep.ofAlgebraAutOnUnits ℚ_[q] Ω) := by
  rw [← map_sub]
  apply unitsInflate₂_mem_levelCoboundaries₂_of_mem_coboundaries₂ q hL
  have : H2π (Rep.ofAlgebraAutOnUnits ℚ_[q] L) (c - c') = 0 := by rw [map_sub, h, sub_self]
  exact (H2π_eq_zero_iff _).1 this

lemma eb_restrictNormalHom_eq_one_of_forall {S : Set Ω} (hLS : L ≤ IntermediateField.adjoin ℚ_[q] S)
    (s : Ω ≃ₐ[ℚ_[q]] Ω) (hs : ∀ x ∈ S, s x = x) : AlgEquiv.restrictNormalHom L s = 1 := by
  have hle : IntermediateField.adjoin ℚ_[q] S ≤ IntermediateField.fixedField (Subgroup.zpowers s) := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    rintro g ⟨k, rfl⟩
    change (s ^ k) x = x
    have h1 : s x = x := hs x hx
    have hsymm : s.symm x = x := by
      conv_lhs => rw [← h1]
      exact s.symm_apply_apply x
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [zpow_add_one, AlgEquiv.mul_apply, h1]; exact ih
    | pred k ih =>
      rw [sub_eq_add_neg, zpow_add, zpow_neg_one, AlgEquiv.mul_apply, AlgEquiv.aut_inv, hsymm]; exact ih
  apply AlgEquiv.ext
  intro y
  apply Subtype.ext
  have hy : s (y : Ω) = y := by
    have hmem := hle (hLS y.2)
    rw [IntermediateField.mem_fixedField_iff] at hmem
    exact hmem s (Subgroup.mem_zpowers s)
  change ((AlgEquiv.restrictNormal s L y : L) : Ω) = y
  have := AlgEquiv.restrictNormal_commutes s L y
  simp only [IntermediateField.algebraMap_apply] at this
  rw [this, hy]

lemma eb_exists_level_fixing_rootsOfUnity (N : ℕ) (hN : 0 < N) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : (Ω ≃ₐ[ℚ_[q]] Ω), localGaloisToGlobal q s ∈ F.fixingSubgroup →
        ∀ x : Ω, x ^ N = 1 → s x = x := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero (N : AlgebraicClosure ℚ) := NeZero.charZero
  obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ : AlgebraicClosure ℚ, IsPrimitiveRoot ξ N := HasEnoughRootsOfUnity.prim
  refine ⟨IntermediateField.adjoin ℚ {ξ₀}, ?_, ?_⟩
  · exact IntermediateField.adjoin.finiteDimensional (hξ₀.isIntegral hN).tower_top
  · intro s hs x hx
    have hfix : localGaloisToGlobal q s ξ₀ = ξ₀ :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp hs ξ₀ (IntermediateField.mem_adjoin_simple_self ℚ ξ₀)
    have hsξ : s (padicEmbedding q ξ₀) = padicEmbedding q ξ₀ := by
      rw [← padicEmbedding_localGaloisToGlobal, hfix]
    have hprim : IsPrimitiveRoot (padicEmbedding q ξ₀) N :=
      hξ₀.map_of_injective (padicEmbedding q).toRingHom.injective
    obtain ⟨i, -, rfl⟩ := hprim.eq_pow_of_pow_eq_one hx
    rw [map_pow, hsξ]

lemma eb_hasLevel_of_adjoin_union {S₂ : Set Ω} {N : ℕ} (hN : 0 < N)
    (hLS : L ≤ IntermediateField.adjoin ℚ_[q] (S₂ ∪ {x : Ω | x ^ N = 1}))
    (F₂ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F₂]
    (hF₂ : ∀ s : (Ω ≃ₐ[ℚ_[q]] Ω), localGaloisToGlobal q s ∈ F₂.fixingSubgroup → ∀ x ∈ S₂, s x = x) :
    eb_HasLevel q L := by
  obtain ⟨F₀, hF₀, hfix₀⟩ := eb_exists_level_fixing_rootsOfUnity q N hN
  haveI := hF₀
  refine ⟨F₂ ⊔ F₀, inferInstance, fun s hs => ?_⟩
  apply eb_restrictNormalHom_eq_one_of_forall q L hLS s
  rintro x (hx | hx)
  · exact hF₂ s (IntermediateField.fixingSubgroup_antitone le_sup_left hs) x hx
  · exact hfix₀ s (IntermediateField.fixingSubgroup_antitone le_sup_right hs) x hx

end eb_lift

theorem stageC (q : Nat.Primes) [Fact ((q : ℕ)).Prime] (p : ℕ) [Fact p.Prime]
    (L₂ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L₂] [IsGalois ℚ_[q] L₂]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L₂] [FaithfulSMul G L₂] [MulDistribMulAction G (↥L₂)ˣ]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L₂ x = algebraMap ℚ_[q] L₂ x)
    (hcompat : ∀ (g : G) (v : (↥L₂)ˣ), ((g • v : (↥L₂)ˣ) : L₂) = g • (v : L₂))
    (π : primeLocalGaloisGroup q →* G) (hπs : Function.Surjective π)
    (hact : ∀ (τ : primeLocalGaloisGroup q) (y : L₂), ((π τ • y : L₂) : PadicAlgCl q) = (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) y)
    (hlev : ∃ F₁ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₁ ∧
      ∀ τ : primeLocalGaloisGroup q, localGaloisToGlobal q (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) ∈ F₁.fixingSubgroup → π τ = 1)
    (x₂ : cocycles₂ (Rep.ofMulDistribMulAction G (↥L₂)ˣ))
    (X : levelCocycles₂ (primeLocalToGlobal q) (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
    (hX : ∀ g h : primeLocalGaloisGroup q, ((Additive.toMul ((X : primeLocalGaloisGroup q × primeLocalGaloisGroup q → (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) (g, h)) : (PadicAlgCl q)ˣ) : PadicAlgCl q) =
      (((Additive.toMul (x₂ (π g, π h)) : (↥L₂)ˣ) : L₂) : PadicAlgCl q))
    (φ : (L0 q p) ≃ₐ[ℚ_[q]] (L0 q p)) (hs : ∀ σ, σ ∈ Subgroup.zpowers φ) (hfin : IsOfFinOrder φ)
    (α : (↥(L0 q p))ˣ)
    (hc : carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p)) (Additive.ofMul α) ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p)))
    [Normal ℚ_[q] (L0 q p)]
    (hB : ∀ (M : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] M] [IsGalois ℚ_[q] M]
      (hL₂M : L₂ ≤ M) (hL₀M : L0 q p ≤ M)
      (r₂ : (M ≃ₐ[ℚ_[q]] M) →* G) (_ : Function.Surjective r₂)
      (_ : ∀ (h : M ≃ₐ[ℚ_[q]] M) (x : L₂), ((r₂ h • x : L₂) : PadicAlgCl q) = ((h ⟨(x : PadicAlgCl q), hL₂M x.2⟩ : M) : PadicAlgCl q))
      (ι₂ : Rep.res r₂ (Rep.ofMulDistribMulAction G (↥L₂)ˣ) ⟶ Rep.ofAlgebraAutOnUnits ℚ_[q] M)
      (_ : ∀ v : (↥L₂)ˣ, (((Additive.toMul (ι₂.hom (Additive.ofMul v)) : (↥M)ˣ) : M) : PadicAlgCl q) = ((v : L₂) : PadicAlgCl q))
      (r₀ : (M ≃ₐ[ℚ_[q]] M) →* ((L0 q p) ≃ₐ[ℚ_[q]] (L0 q p))) (_ : Function.Surjective r₀)
      (_ : ∀ (h : M ≃ₐ[ℚ_[q]] M) (x : L0 q p), ((r₀ h x : L0 q p) : PadicAlgCl q) = ((h ⟨(x : PadicAlgCl q), hL₀M x.2⟩ : M) : PadicAlgCl q))
      (ι₀ : Rep.res r₀ (Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p)) ⟶ Rep.ofAlgebraAutOnUnits ℚ_[q] M)
      (_ : ∀ v : (↥(L0 q p))ˣ, (((Additive.toMul (ι₀.hom (Additive.ofMul v)) : (↥M)ˣ) : M) : PadicAlgCl q) = ((v : L0 q p) : PadicAlgCl q)),
      (groupCohomology.map r₂ ι₂ 2).hom ((H2π (Rep.ofMulDistribMulAction G (↥L₂)ˣ)).hom x₂) =
        (groupCohomology.map r₀ ι₀ 2).hom ((H2π (Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p))).hom
          ⟨carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p)) (Additive.ofMul α), hc⟩)) :
    (fun g : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) =>
        (show Additive (PadicAlgCl q)ˣ from
          (X : primeLocalGaloisGroup q × primeLocalGaloisGroup q → (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) g))
      - unitsInflate₂ (L0 q p)
          (carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p)) (Additive.ofMul α))
      ∈ levelCoboundaries₂ (localGaloisToGlobal q) (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) := by
  classical

  haveI : Normal ℚ_[q] ↥L₂ := inferInstance
  haveI : FiniteDimensional ℚ_[q] ↥(L0 q p) := Module.finite_of_finrank_pos (by
    rw [(PadicAlgCl.finrank_adjoin_rootsOfUnity_eq_and_forall_norm_eq_zpow (q : ℕ) p (Fact.out : p.Prime).pos).2.1]
    exact (Fact.out : p.Prime).pos)
  let M : IntermediateField ℚ_[q] (PadicAlgCl q) := L₂ ⊔ L0 q p
  haveI : FiniteDimensional ℚ_[q] ↥M := IntermediateField.finiteDimensional_sup L₂ (L0 q p)
  haveI : Normal ℚ_[q] ↥M := IntermediateField.normal_sup ℚ_[q] (PadicAlgCl q) L₂ (L0 q p)
  haveI : IsGalois ℚ_[q] ↥M := ⟨⟩
  have hL₂M : L₂ ≤ M := le_sup_left
  have hL₀M : L0 q p ≤ M := le_sup_right
  let resM : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) →* (↥M ≃ₐ[ℚ_[q]] ↥M) := AlgEquiv.restrictNormalHom ↥M
  have hresMs : Function.Surjective resM := AlgEquiv.restrictNormalHom_surjective (PadicAlgCl q)
  have hresM : ∀ (τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) (y : ↥M), ((resM τ y : ↥M) : PadicAlgCl q) = τ (y : PadicAlgCl q) := by
    intro τ y
    have := AlgEquiv.restrictNormal_commutes τ ↥M y
    simp only [IntermediateField.algebraMap_apply] at this
    exact this
  have hres0 : ∀ (τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) (y : ↥(L0 q p)),
      ((AlgEquiv.restrictNormalHom ↥(L0 q p) τ y : ↥(L0 q p)) : PadicAlgCl q) = τ (y : PadicAlgCl q) := by
    intro τ y
    have := AlgEquiv.restrictNormal_commutes τ ↥(L0 q p) y
    simp only [IntermediateField.algebraMap_apply] at this
    exact this

  have hfixM : ∀ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q, resM τ = 1 → ∀ y : PadicAlgCl q, y ∈ M → τ y = y := by
    intro τ hτ y hy
    have := hresM τ ⟨y, hy⟩
    rw [hτ] at this
    exact this.symm

  have hker₂ : resM.ker ≤ π.ker := by
    intro τ hτ
    change resM τ = 1 at hτ
    change π τ = 1
    apply FaithfulSMul.eq_of_smul_eq_smul (α := ↥L₂)
    intro y
    apply Subtype.ext
    rw [hact, one_smul]
    exact hfixM τ hτ y (hL₂M y.2)
  let r₂ : (↥M ≃ₐ[ℚ_[q]] ↥M) →* G :=
    MonoidHom.liftOfRightInverse resM (Function.surjInv hresMs) (Function.rightInverse_surjInv hresMs) ⟨π, hker₂⟩
  have hr₂c : ∀ τ, r₂ (resM τ) = π τ := fun τ =>
    MonoidHom.liftOfRightInverse_comp_apply resM (Function.surjInv hresMs) (Function.rightInverse_surjInv hresMs) ⟨π, hker₂⟩ τ
  have hr₂s : Function.Surjective r₂ := fun g => by
    obtain ⟨τ, rfl⟩ := hπs g
    exact ⟨resM τ, hr₂c τ⟩
  have hr₂ : ∀ (h : ↥M ≃ₐ[ℚ_[q]] ↥M) (x : ↥L₂), ((r₂ h • x : ↥L₂) : PadicAlgCl q) = ((h ⟨(x : PadicAlgCl q), hL₂M x.2⟩ : ↥M) : PadicAlgCl q) := by
    intro h x
    obtain ⟨τ, rfl⟩ := hresMs h
    rw [hr₂c, hact, hresM]
  let ι₂l : Additive (↥L₂)ˣ →ₗ[ℤ] Additive (↥M)ˣ :=
    (MonoidHom.toAdditive (Units.map ((IntermediateField.inclusion hL₂M : ↥L₂ →ₐ[ℚ_[q]] ↥M) : ↥L₂ →* ↥M))).toIntLinearMap
  have hι₂l : ∀ v : (↥L₂)ˣ, (((Additive.toMul (ι₂l (Additive.ofMul v)) : (↥M)ˣ) : ↥M) : PadicAlgCl q) = ((v : ↥L₂) : PadicAlgCl q) := fun _ => rfl
  let ι₂ : Rep.res r₂ (Rep.ofMulDistribMulAction G (↥L₂)ˣ) ⟶ Rep.ofAlgebraAutOnUnits ℚ_[q] ↥M :=
    Rep.ofHom ⟨ι₂l, fun h => LinearMap.ext fun a => by
      show ι₂l ((Rep.ofMulDistribMulAction G (↥L₂)ˣ).ρ (r₂ h) a) = (Rep.ofMulDistribMulAction (↥M ≃ₐ[ℚ_[q]] ↥M) (↥M)ˣ).ρ h (ι₂l a)
      rw [Rep.ofMulDistribMulAction_ρ_apply_apply, Rep.ofMulDistribMulAction_ρ_apply_apply]
      obtain ⟨v, rfl⟩ := (Additive.ofMul (α := (↥L₂)ˣ)).surjective a
      change Additive.ofMul (Units.map ((IntermediateField.inclusion hL₂M : ↥L₂ →ₐ[ℚ_[q]] ↥M) : ↥L₂ →* ↥M) (r₂ h • v)) =
        Additive.ofMul (h • Units.map ((IntermediateField.inclusion hL₂M : ↥L₂ →ₐ[ℚ_[q]] ↥M) : ↥L₂ →* ↥M) v)
      congr 1
      apply Units.ext
      apply Subtype.ext
      rw [AlgEquiv.smul_units_def, Units.coe_map, Units.coe_map, Units.coe_map]
      change (((IntermediateField.inclusion hL₂M) ((r₂ h • v : (↥L₂)ˣ) : ↥L₂) : ↥M) : PadicAlgCl q) =
        ((h ((IntermediateField.inclusion hL₂M) ((v : ↥L₂))) : ↥M) : PadicAlgCl q)
      rw [IntermediateField.coe_inclusion, hcompat, hr₂]
      rfl⟩
  have hι₂ : ∀ v : (↥L₂)ˣ, (((Additive.toMul (ι₂.hom (Additive.ofMul v)) : (↥M)ˣ) : ↥M) : PadicAlgCl q) = ((v : ↥L₂) : PadicAlgCl q) :=
    fun _ => rfl

  have hker₀ : resM.ker ≤ (AlgEquiv.restrictNormalHom ↥(L0 q p) : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) →* _).ker := by
    intro τ hτ
    change resM τ = 1 at hτ
    change AlgEquiv.restrictNormalHom ↥(L0 q p) τ = 1
    apply AlgEquiv.ext
    intro y
    apply Subtype.ext
    rw [hres0]
    exact hfixM τ hτ y (hL₀M y.2)
  let r₀ : (↥M ≃ₐ[ℚ_[q]] ↥M) →* (↥(L0 q p) ≃ₐ[ℚ_[q]] ↥(L0 q p)) :=
    MonoidHom.liftOfRightInverse resM (Function.surjInv hresMs) (Function.rightInverse_surjInv hresMs)
      ⟨AlgEquiv.restrictNormalHom ↥(L0 q p), hker₀⟩
  have hr₀c : ∀ τ, r₀ (resM τ) = AlgEquiv.restrictNormalHom ↥(L0 q p) τ := fun τ =>
    MonoidHom.liftOfRightInverse_comp_apply resM (Function.surjInv hresMs) (Function.rightInverse_surjInv hresMs) ⟨_, hker₀⟩ τ
  have hr₀s : Function.Surjective r₀ := fun g => by
    obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ_[q]) (K₁ := ↥(L0 q p)) (PadicAlgCl q) g
    exact ⟨resM τ, hr₀c τ⟩
  have hr₀ : ∀ (h : ↥M ≃ₐ[ℚ_[q]] ↥M) (x : ↥(L0 q p)), ((r₀ h x : ↥(L0 q p)) : PadicAlgCl q) = ((h ⟨(x : PadicAlgCl q), hL₀M x.2⟩ : ↥M) : PadicAlgCl q) := by
    intro h x
    obtain ⟨τ, rfl⟩ := hresMs h
    rw [hr₀c, hres0, hresM]
  let ι₀l : Additive (↥(L0 q p))ˣ →ₗ[ℤ] Additive (↥M)ˣ :=
    (MonoidHom.toAdditive (Units.map ((IntermediateField.inclusion hL₀M : ↥(L0 q p) →ₐ[ℚ_[q]] ↥M) : ↥(L0 q p) →* ↥M))).toIntLinearMap
  let ι₀ : Rep.res r₀ (Rep.ofAlgebraAutOnUnits ℚ_[q] ↥(L0 q p)) ⟶ Rep.ofAlgebraAutOnUnits ℚ_[q] ↥M :=
    Rep.ofHom ⟨ι₀l, fun h => LinearMap.ext fun a => by
      show ι₀l ((Rep.ofMulDistribMulAction (↥(L0 q p) ≃ₐ[ℚ_[q]] ↥(L0 q p)) (↥(L0 q p))ˣ).ρ (r₀ h) a) =
        (Rep.ofMulDistribMulAction (↥M ≃ₐ[ℚ_[q]] ↥M) (↥M)ˣ).ρ h (ι₀l a)
      rw [Rep.ofMulDistribMulAction_ρ_apply_apply, Rep.ofMulDistribMulAction_ρ_apply_apply]
      obtain ⟨v, rfl⟩ := (Additive.ofMul (α := (↥(L0 q p))ˣ)).surjective a
      change Additive.ofMul (Units.map ((IntermediateField.inclusion hL₀M : ↥(L0 q p) →ₐ[ℚ_[q]] ↥M) : ↥(L0 q p) →* ↥M) (r₀ h • v)) =
        Additive.ofMul (h • Units.map ((IntermediateField.inclusion hL₀M : ↥(L0 q p) →ₐ[ℚ_[q]] ↥M) : ↥(L0 q p) →* ↥M) v)
      congr 1
      apply Units.ext
      apply Subtype.ext
      rw [AlgEquiv.smul_units_def, AlgEquiv.smul_units_def, Units.coe_map, Units.coe_map, Units.coe_map]
      change (((IntermediateField.inclusion hL₀M) ((r₀ h) (v : ↥(L0 q p))) : ↥M) : PadicAlgCl q) =
        ((h ((IntermediateField.inclusion hL₀M) ((v : ↥(L0 q p)))) : ↥M) : PadicAlgCl q)
      rw [IntermediateField.coe_inclusion, hr₀]
      rfl⟩
  have hι₀ : ∀ v : (↥(L0 q p))ˣ, (((Additive.toMul (ι₀.hom (Additive.ofMul v)) : (↥M)ˣ) : ↥M) : PadicAlgCl q) = ((v : ↥(L0 q p)) : PadicAlgCl q) :=
    fun _ => rfl

  have key := hB M hL₂M hL₀M r₂ hr₂s hr₂ ι₂ hι₂ r₀ hr₀s hr₀ ι₀ hι₀
  have key' : H2π (Rep.ofAlgebraAutOnUnits ℚ_[q] ↥M) (mapCocycles₂ r₂ ι₂ x₂) =
      H2π (Rep.ofAlgebraAutOnUnits ℚ_[q] ↥M) (mapCocycles₂ r₀ ι₀ ⟨carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p)) (Additive.ofMul α), hc⟩) := by
    have e₂ := congrArg (fun f => (ConcreteCategory.hom f) x₂) (H2π_comp_map (A := Rep.ofMulDistribMulAction G (↥L₂)ˣ) r₂ ι₂)
    have e₀ := congrArg (fun f => (ConcreteCategory.hom f) ⟨carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p)) (Additive.ofMul α), hc⟩)
      (H2π_comp_map (A := Rep.ofAlgebraAutOnUnits ℚ_[q] ↥(L0 q p)) r₀ ι₀)
    simp only [ConcreteCategory.comp_apply] at e₂ e₀
    exact e₂.symm.trans (key.trans e₀)

  have hq2 : 2 ≤ (q : ℕ) := (Fact.out : ((q : ℕ)).Prime).two_le
  have hN : 0 < (q : ℕ) ^ p - 1 := by
    have : 1 < (q : ℕ) ^ p := Nat.one_lt_pow (Fact.out : p.Prime).ne_zero (by omega)
    omega
  obtain ⟨F₁, hF₁, hF₁π⟩ := hlev
  haveI := hF₁
  have hLS : M ≤ IntermediateField.adjoin ℚ_[q] ((L₂ : Set (PadicAlgCl q)) ∪ {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}) := by
    apply sup_le
    · intro x hx
      exact IntermediateField.subset_adjoin ℚ_[q] _ (Set.mem_union_left _ hx)
    · exact IntermediateField.adjoin.mono ℚ_[q] _ _ Set.subset_union_right
  have hF₁fix : ∀ s : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q), localGaloisToGlobal q s ∈ F₁.fixingSubgroup →
      ∀ x ∈ (L₂ : Set (PadicAlgCl q)), s x = x := by
    intro s hs x hx
    have h1 : π s = 1 := hF₁π s hs
    have := hact s ⟨x, hx⟩
    rw [h1, one_smul] at this
    exact this.symm
  have hLev : eb_HasLevel (q : ℕ) M := eb_hasLevel_of_adjoin_union (q : ℕ) M hN hLS F₁ hF₁fix
  have hdiff := eb_unitsInflate₂_sub_mem_levelCoboundaries₂_of_H2π_eq (q : ℕ) hLev _ _ key'

  convert hdiff using 2
  ·
    funext gh
    obtain ⟨g, h⟩ := gh
    apply (Additive.toMul (α := (PadicAlgCl q)ˣ)).injective
    apply Units.ext
    refine (hX g h).trans ?_
    change _ = (((Additive.toMul (ι₂.hom (x₂ (r₂ (resM g), r₂ (resM h)))) : (↥M)ˣ) : ↥M) : PadicAlgCl q)
    rw [hr₂c, hr₂c]
    rfl
  ·
    funext gh
    obtain ⟨g, h⟩ := gh
    apply (Additive.toMul (α := (PadicAlgCl q)ˣ)).injective
    apply Units.ext
    change ((((Additive.toMul (carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p)) (Additive.ofMul α)
        (AlgEquiv.restrictNormalHom ↥(L0 q p) g, AlgEquiv.restrictNormalHom ↥(L0 q p) h))) : (↥(L0 q p))ˣ) : ↥(L0 q p)) : PadicAlgCl q) =
      (((Additive.toMul (ι₀.hom (carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] (L0 q p)) (Additive.ofMul α)
        (r₀ (resM g), r₀ (resM h)))) : (↥M)ˣ) : ↥M) : PadicAlgCl q)
    rw [hr₀c, hr₀c]
    rfl

namespace A

section RepHom
variable {G : Type} [Group G] {X Y : Type} [CommGroup X] [CommGroup Y] [MulDistribMulAction G X] [MulDistribMulAction G Y]

noncomputable def repHom (f : X →* Y) (hf : ∀ (g : G) (m : X), f (g • m) = g • f m) :
    Rep.ofMulDistribMulAction G X ⟶ Rep.ofMulDistribMulAction G Y :=
  Rep.ofHom ⟨(MonoidHom.toAdditive f).toIntLinearMap, fun g => LinearMap.ext fun x => by
    change Additive.ofMul (f (g • Additive.toMul x)) = Additive.ofMul (g • f (Additive.toMul x))
    rw [hf]⟩

@[scoped simp] theorem repHom_hom_apply (f : X →* Y) (hf : ∀ (g : G) (m : X), f (g • m) = g • f m) (x : Additive X) :
    (repHom f hf).hom x = Additive.ofMul (f (Additive.toMul x)) := rfl

end RepHom

theorem prime_eq_of_natCast_mem {R : Type} [CommRing R] (I : Ideal R) [hI : I.IsPrime] (p₁ p₂ : ℕ)
    (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (h₁ : (p₁ : R) ∈ I) (h₂ : (p₂ : R) ∈ I) : p₁ = p₂ := by
  by_contra hne
  have hcop : Nat.Coprime p₁ p₂ := (Nat.coprime_primes hp₁ hp₂).mpr hne
  obtain ⟨a, b, hab⟩ := hcop.isCoprime
  apply hI.ne_top
  rw [Ideal.eq_top_iff_one]
  have : ((a * p₁ + b * p₂ : ℤ) : R) = 1 := by rw [hab]; simp
  rw [← this]
  push_cast
  exact I.add_mem (I.mul_mem_left _ h₁) (I.mul_mem_left _ h₂)

section C8
variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

noncomputable def vQ : HeightOneSpectrum (𝓞 ℚ) := HeightOneSpectrum.under (𝓞 ℚ) w

noncomputable def qOf : ℕ := (Rat.HeightOneSpectrum.primesEquiv (vQ K w) : Nat.Primes)
scoped instance qOf_prime : Fact (qOf K w).Prime := ⟨(Rat.HeightOneSpectrum.primesEquiv (vQ K w)).2⟩

noncomputable def WExt : (vQ K w).Extension (𝓞 K) := ⟨w, rfl⟩

noncomputable scoped instance algQv : Algebra ((vQ K w).adicCompletion ℚ) (w.adicCompletion K) :=
  (inferInstance : Algebra ((vQ K w).adicCompletion ℚ) ((WExt K w).1.adicCompletion K))

scoped instance finQv : Module.Finite ((vQ K w).adicCompletion ℚ) (w.adicCompletion K) :=
  (inferInstance : Module.Finite ((vQ K w).adicCompletion ℚ) ((WExt K w).1.adicCompletion K))

noncomputable def padicIso : ℚ_[qOf K w] ≃+* (vQ K w).adicCompletion ℚ :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (vQ K w)).symm.toAlgEquiv.toRingEquiv

noncomputable scoped instance algPadicQv : Algebra ℚ_[qOf K w] ((vQ K w).adicCompletion ℚ) := (padicIso K w).toRingHom.toAlgebra

noncomputable scoped instance algPadic : Algebra ℚ_[qOf K w] (w.adicCompletion K) :=
  ((algebraMap ((vQ K w).adicCompletion ℚ) (w.adicCompletion K)).comp (padicIso K w).toRingHom).toAlgebra

scoped instance towerPadic : IsScalarTower ℚ_[qOf K w] ((vQ K w).adicCompletion ℚ) (w.adicCompletion K) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

scoped instance finPadicQv : Module.Finite ℚ_[qOf K w] ((vQ K w).adicCompletion ℚ) :=
  Module.Finite.of_surjective (Algebra.linearMap ℚ_[qOf K w] ((vQ K w).adicCompletion ℚ))
    (padicIso K w).surjective

scoped instance finPadic : Module.Finite ℚ_[qOf K w] (w.adicCompletion K) :=
  Module.Finite.trans ((vQ K w).adicCompletion ℚ) (w.adicCompletion K)

theorem continuous_algebraMap_padic : Continuous (algebraMap ℚ_[qOf K w] (w.adicCompletion K)) := by
  show Continuous (fun x => algebraMap ((vQ K w).adicCompletion ℚ) (w.adicCompletion K) (padicIso K w x))
  apply Continuous.comp
  · exact IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom_continuous ℚ K (WExt K w)
  · exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (vQ K w)).symm.continuous

theorem natCast_qOf_mem : ((qOf K w : ℕ) : 𝓞 K) ∈ w.asIdeal := by
  have h := (Rat.HeightOneSpectrum.natGenerator_dvd_iff (vQ K w) (n := qOf K w)).1 (dvd_refl _)
  rw [Ideal.mem_map_of_equiv] at h
  obtain ⟨x, hx, hxq⟩ := h
  have hx' : algebraMap (𝓞 ℚ) (𝓞 K) x ∈ w.asIdeal := hx
  have hxe : x = ((qOf K w : ℕ) : 𝓞 ℚ) := by
    apply (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).injective
    rw [hxq, map_natCast]
  rw [hxe, map_natCast] at hx'
  exact hx'

variable (E : Type) [Field E] [Algebra E K]

theorem algebraMap_padic_ratCast (r : ℚ) :
    algebraMap ℚ_[qOf K w] (w.adicCompletion K) (r : ℚ_[qOf K w]) = (r : w.adicCompletion K) := by
  rw [map_ratCast]

theorem smul_ratCast (σ : NumberField.PlaceDecomp.decomp E K w) (r : ℚ) :
    σ • (r : w.adicCompletion K) = (r : w.adicCompletion K) := by
  rw [NumberField.PlaceDecomp.smul_def, map_ratCast]

theorem smul_algebraMap_padic (σ : NumberField.PlaceDecomp.decomp E K w) (x : ℚ_[qOf K w]) :
    σ • algebraMap ℚ_[qOf K w] (w.adicCompletion K) x = algebraMap ℚ_[qOf K w] (w.adicCompletion K) x := by
  have hcont := continuous_algebraMap_padic K w
  have h1 : Continuous (fun x : ℚ_[qOf K w] => σ • algebraMap ℚ_[qOf K w] (w.adicCompletion K) x) := by
    have : (fun x : ℚ_[qOf K w] => σ • algebraMap ℚ_[qOf K w] (w.adicCompletion K) x) =
        (NumberField.PlaceDecomp.actRingEquiv σ) ∘ (algebraMap ℚ_[qOf K w] (w.adicCompletion K)) := by
      funext x; exact NumberField.PlaceDecomp.smul_def σ _
    rw [this]
    exact (NumberField.PlaceDecomp.continuous_actRingEquiv σ).comp hcont
  have key := DenseRange.equalizer (Padic.denseRange_ratCast (qOf K w)) h1 hcont (by
    funext r
    show σ • algebraMap ℚ_[qOf K w] (w.adicCompletion K) (r : ℚ_[qOf K w]) = algebraMap ℚ_[qOf K w] (w.adicCompletion K) (r : ℚ_[qOf K w])
    rw [algebraMap_padic_ratCast, smul_ratCast])
  exact congrFun key x

theorem smul_coe (σ : NumberField.PlaceDecomp.decomp E K w) (k : K) :
    σ • ((WithVal.toVal (w.valuation K) k : WithVal (w.valuation K)) : w.adicCompletion K) =
      ((WithVal.toVal (w.valuation K) ((σ : K ≃ₐ[E] K) k) : WithVal (w.valuation K)) : w.adicCompletion K) := by
  rw [NumberField.PlaceDecomp.smul_def, NumberField.PlaceDecomp.actRingEquiv_coe, WithVal.congr_apply]
  rfl

theorem faithful_Kw : FaithfulSMul (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K) := by
  refine ⟨fun {σ τ} h => ?_⟩
  apply Subtype.ext
  apply AlgEquiv.ext
  intro k
  have hk := h ((WithVal.toVal (w.valuation K) k : WithVal (w.valuation K)) : w.adicCompletion K)
  rw [smul_coe, smul_coe] at hk
  have := UniformSpace.Completion.coe_injective _ (congrArg (fun z => z.toCompletion) hk)
  exact congrArg WithVal.ofVal this

variable (Φ : w.adicCompletion K →+* PadicAlgCl (qOf K w)) (hΦc : Continuous Φ)

include hΦc in

theorem map_algebraMap_padic (c : ℚ_[qOf K w]) :
    Φ (algebraMap ℚ_[qOf K w] (w.adicCompletion K) c) = algebraMap ℚ_[qOf K w] (PadicAlgCl (qOf K w)) c := by
  have h1 : Continuous (fun c : ℚ_[qOf K w] => Φ (algebraMap ℚ_[qOf K w] (w.adicCompletion K) c)) :=
    hΦc.comp (continuous_algebraMap_padic K w)
  have h2 : Continuous (algebraMap ℚ_[qOf K w] (PadicAlgCl (qOf K w))) := continuous_algebraMap _ _
  have key := DenseRange.equalizer (Padic.denseRange_ratCast (qOf K w)) h1 h2 (by
    funext r
    show Φ (algebraMap ℚ_[qOf K w] (w.adicCompletion K) (r : ℚ_[qOf K w])) = algebraMap ℚ_[qOf K w] (PadicAlgCl (qOf K w)) (r : ℚ_[qOf K w])
    rw [map_ratCast, map_ratCast, map_ratCast])
  exact congrFun key c

noncomputable def Φa : w.adicCompletion K →ₐ[ℚ_[qOf K w]] PadicAlgCl (qOf K w) :=
  { Φ with commutes' := map_algebraMap_padic K w Φ hΦc }

@[scoped simp] theorem Φa_apply (y : w.adicCompletion K) : Φa K w Φ hΦc y = Φ y := rfl

noncomputable def Limg : IntermediateField ℚ_[qOf K w] (PadicAlgCl (qOf K w)) := (Φa K w Φ hΦc).fieldRange

noncomputable def Φ₂ : w.adicCompletion K ≃ₐ[ℚ_[qOf K w]] Limg K w Φ hΦc := AlgEquiv.ofInjectiveField (Φa K w Φ hΦc)

theorem coe_Φ₂ (y : w.adicCompletion K) : ((Φ₂ K w Φ hΦc y : Limg K w Φ hΦc) : PadicAlgCl (qOf K w)) = Φ y := rfl

theorem apply_Φ₂_symm (y : Limg K w Φ hΦc) : Φ ((Φ₂ K w Φ hΦc).symm y) = (y : PadicAlgCl (qOf K w)) := by
  rw [← coe_Φ₂ K w Φ hΦc, AlgEquiv.apply_symm_apply]

scoped instance finLimg : FiniteDimensional ℚ_[qOf K w] (Limg K w Φ hΦc) :=
  Module.Finite.equiv (Φ₂ K w Φ hΦc).toLinearEquiv

@[reducible] noncomputable def actImg : MulSemiringAction (NumberField.PlaceDecomp.decomp E K w) (Limg K w Φ hΦc) where
  smul σ y := Φ₂ K w Φ hΦc (σ • (Φ₂ K w Φ hΦc).symm y)
  one_smul y := by
    show Φ₂ K w Φ hΦc ((1 : NumberField.PlaceDecomp.decomp E K w) • (Φ₂ K w Φ hΦc).symm y) = y
    rw [one_smul, AlgEquiv.apply_symm_apply]
  mul_smul σ τ y := by
    show Φ₂ K w Φ hΦc ((σ * τ) • (Φ₂ K w Φ hΦc).symm y) =
      Φ₂ K w Φ hΦc (σ • (Φ₂ K w Φ hΦc).symm (Φ₂ K w Φ hΦc (τ • (Φ₂ K w Φ hΦc).symm y)))
    rw [AlgEquiv.symm_apply_apply, mul_smul]
  smul_zero σ := by show Φ₂ K w Φ hΦc (σ • (Φ₂ K w Φ hΦc).symm 0) = 0; rw [map_zero, smul_zero, map_zero]
  smul_add σ x y := by
    show Φ₂ K w Φ hΦc (σ • (Φ₂ K w Φ hΦc).symm (x + y)) = Φ₂ K w Φ hΦc (σ • (Φ₂ K w Φ hΦc).symm x) + Φ₂ K w Φ hΦc (σ • (Φ₂ K w Φ hΦc).symm y)
    rw [map_add, smul_add, map_add]
  smul_one σ := by show Φ₂ K w Φ hΦc (σ • (Φ₂ K w Φ hΦc).symm 1) = 1; rw [map_one, smul_one, map_one]
  smul_mul σ x y := by
    show Φ₂ K w Φ hΦc (σ • (Φ₂ K w Φ hΦc).symm (x * y)) = Φ₂ K w Φ hΦc (σ • (Φ₂ K w Φ hΦc).symm x) * Φ₂ K w Φ hΦc (σ • (Φ₂ K w Φ hΦc).symm y)
    rw [map_mul, MulSemiringAction.smul_mul, map_mul]

theorem actImg_smul_def (σ : NumberField.PlaceDecomp.decomp E K w) (y : Limg K w Φ hΦc) :
    @HSMul.hSMul _ _ _ (@instHSMul _ _ (actImg K w E Φ hΦc).toSMul) σ y = Φ₂ K w Φ hΦc (σ • (Φ₂ K w Φ hΦc).symm y) := rfl

theorem Φ₂_smul (σ : NumberField.PlaceDecomp.decomp E K w) (x : w.adicCompletion K) :
    Φ₂ K w Φ hΦc (σ • x) = @HSMul.hSMul _ _ _ (@instHSMul _ _ (actImg K w E Φ hΦc).toSMul) σ (Φ₂ K w Φ hΦc x) := by
  rw [actImg_smul_def, AlgEquiv.symm_apply_apply]

theorem Φ₂_symm_smul (σ : NumberField.PlaceDecomp.decomp E K w) (y : Limg K w Φ hΦc) :
    (Φ₂ K w Φ hΦc).symm (@HSMul.hSMul _ _ _ (@instHSMul _ _ (actImg K w E Φ hΦc).toSMul) σ y) = σ • (Φ₂ K w Φ hΦc).symm y := by
  rw [actImg_smul_def, AlgEquiv.symm_apply_apply]

theorem coe_actImg_smul (σ : NumberField.PlaceDecomp.decomp E K w) (y : Limg K w Φ hΦc) :
    ((@HSMul.hSMul _ _ _ (@instHSMul _ _ (actImg K w E Φ hΦc).toSMul) σ y : Limg K w Φ hΦc) : PadicAlgCl (qOf K w)) =
      Φ (σ • (Φ₂ K w Φ hΦc).symm y) := rfl

theorem faithful_img : @FaithfulSMul (NumberField.PlaceDecomp.decomp E K w) (Limg K w Φ hΦc) (actImg K w E Φ hΦc).toSMul := by
  refine @FaithfulSMul.mk _ _ (actImg K w E Φ hΦc).toSMul (fun {σ τ} h => ?_)
  haveI := faithful_Kw K w E
  apply FaithfulSMul.eq_of_smul_eq_smul (α := w.adicCompletion K)
  intro x
  apply (Φ₂ K w Φ hΦc).injective
  rw [Φ₂_smul, Φ₂_smul]
  exact h _

theorem actImg_smul_algebraMap (hfix : ∀ (σ : NumberField.PlaceDecomp.decomp E K w) (c : ℚ_[qOf K w]),
      σ • algebraMap ℚ_[qOf K w] (w.adicCompletion K) c = algebraMap ℚ_[qOf K w] (w.adicCompletion K) c)
    (σ : NumberField.PlaceDecomp.decomp E K w) (c : ℚ_[qOf K w]) :
    @HSMul.hSMul _ _ _ (@instHSMul _ _ (actImg K w E Φ hΦc).toSMul) σ (algebraMap ℚ_[qOf K w] (Limg K w Φ hΦc) c) =
      algebraMap ℚ_[qOf K w] (Limg K w Φ hΦc) c := by
  rw [actImg_smul_def, show (Φ₂ K w Φ hΦc).symm (algebraMap ℚ_[qOf K w] (Limg K w Φ hΦc) c) =
    algebraMap ℚ_[qOf K w] (w.adicCompletion K) c from (Φ₂ K w Φ hΦc).symm.commutes c, hfix, AlgEquiv.commutes]

end C8

end A
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_inflate_sub_unitsInflate2_carryFun_mem_levelCoboundaries2.F2a.A"

theorem stageA {p : ℕ} [Fact p.Prime] (q : Nat.Primes) [Fact ((q : ℕ)).Prime]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (w : HeightOneSpectrum (𝓞 ↥F))
    (hpD : p ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
    (hΦ : ∀ x : ↥F, Φ (algebraMap ↥F (w.adicCompletion ↥F) x) = padicEmbedding q (σ (x : AlgebraicClosure ℚ)))
    (hΦc : Continuous Φ)
    (π : primeLocalGaloisGroup q →* ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))
    (hπ : ∀ τ : primeLocalGaloisGroup q, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ))
    (hπs : Function.Surjective π)
    (hequiv : ∀ (τ : primeLocalGaloisGroup q) (x : w.adicCompletion ↥F),
      Φ (π τ • x) = (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (Φ x))
    (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L')ˣ]
    (Φ' : w.adicCompletion ↥F ≃+* L')
    (hfix' : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
    (hcompat' : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
    (hΦ' : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : w.adicCompletion ↥F), Φ' (g • x) = g • Φ' x)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
    (hK₀ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) K₀)
    (θ' : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L')ˣ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
    (hθ' : ∀ v : (↥L')ˣ, ((Additive.toMul (θ'.hom (Additive.ofMul v)) : (w.adicCompletion ↥F)ˣ) : w.adicCompletion ↥F) = Φ'.symm (v : L'))
    (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L')ˣ))
    (hu' : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) K₀ u')
    (m : ℤ) (z : groupCohomology (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) 2)
    (hz : z = m • ((Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) / p) •
      (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) θ' 2).hom u'))
    (x : cocycles₂ (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ))
    (hx : (H2π (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)).hom x = z)
    (X : levelCocycles₂ (primeLocalToGlobal q) (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
    (hX : ∀ g h : primeLocalGaloisGroup q, Additive.toMul ((X : primeLocalGaloisGroup q × primeLocalGaloisGroup q → (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) (g, h)) =
      Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q) (Additive.toMul ((x : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) × ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) → Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) (π g, π h)))) :
    ∃ (L₂ : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] L₂)
      (_ : MulSemiringAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) L₂) (_ : FaithfulSMul (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) L₂)
      (_ : MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L₂)ˣ) (_ : IsGalois ℚ_[q] L₂)
      (u₂ : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L₂)ˣ))
      (x₂ : cocycles₂ (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L₂)ˣ)),
      (∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (c : ℚ_[q]), g • algebraMap ℚ_[q] L₂ c = algebraMap ℚ_[q] L₂ c) ∧
      (∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (v : (↥L₂)ˣ), ((g • v : (↥L₂)ˣ) : L₂) = g • (v : L₂)) ∧
      (∀ (τ : primeLocalGaloisGroup q) (y : L₂), ((π τ • y : L₂) : PadicAlgCl q) = (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) y) ∧
      ExtCitation.LocalLevel.IsBase q L₂ (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) ⊥ ∧
      ExtCitation.LocalLevel.IsLocalFundamentalClass q L₂ (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) ⊥ u₂ ∧
      (H2π (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L₂)ˣ)).hom x₂ =
        m • ((Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) / p) • u₂) ∧
      (∀ g h : primeLocalGaloisGroup q, ((Additive.toMul ((X : primeLocalGaloisGroup q × primeLocalGaloisGroup q → (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) (g, h)) : (PadicAlgCl q)ˣ) : PadicAlgCl q) =
        (((Additive.toMul (x₂ (π g, π h)) : (↥L₂)ˣ) : L₂) : PadicAlgCl q)) ∧
      (∃ F₁ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₁ ∧
        ∀ τ : primeLocalGaloisGroup q, localGaloisToGlobal q (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) ∈ F₁.fixingSubgroup → π τ = 1) := by
  classical

  obtain ⟨hball', hqw⟩ :=
    NumberField.PlaceDecomp.mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv ↥F w (q : ℕ) L' Φ'
  have hqeq : (q : ℕ) = A.qOf ↥F w :=
    A.prime_eq_of_natCast_mem w.asIdeal _ _ q.2 (A.qOf_prime ↥F w).out hqw (A.natCast_qOf_mem ↥F w)
  obtain ⟨qn, hqn⟩ := q
  change qn = A.qOf ↥F w at hqeq
  subst hqeq

  letI act : MulSemiringAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (A.Limg ↥F w Φ hΦc) := A.actImg ↥F w ℚ Φ hΦc
  letI actU : MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (↥(A.Limg ↥F w Φ hΦc))ˣ := Units.mulDistribMulActionRight
  haveI hfaith : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (A.Limg ↥F w Φ hΦc) := A.faithful_img ↥F w ℚ Φ hΦc

  have hfixKw : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (c : ℚ_[A.qOf ↥F w]),
      g • algebraMap ℚ_[A.qOf ↥F w] (w.adicCompletion ↥F) c = algebraMap ℚ_[A.qOf ↥F w] (w.adicCompletion ↥F) c :=
    A.smul_algebraMap_padic ↥F w ℚ
  have hG₂ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (c : ℚ_[A.qOf ↥F w]), g • algebraMap ℚ_[A.qOf ↥F w] (A.Limg ↥F w Φ hΦc) c =
      algebraMap ℚ_[A.qOf ↥F w] (A.Limg ↥F w Φ hΦc) c := A.actImg_smul_algebraMap ↥F w ℚ Φ hΦc hfixKw
  have hcompat₂ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (v : (↥(A.Limg ↥F w Φ hΦc))ˣ), ((g • v : (↥(A.Limg ↥F w Φ hΦc))ˣ) : A.Limg ↥F w Φ hΦc) = g • (v : A.Limg ↥F w Φ hΦc) :=
    fun _ _ => rfl
  have hact₂ : ∀ (τ : primeLocalGaloisGroup ⟨A.qOf ↥F w, hqn⟩) (y : A.Limg ↥F w Φ hΦc),
      ((π τ • y : A.Limg ↥F w Φ hΦc) : PadicAlgCl (A.qOf ↥F w)) = (show PadicAlgCl (A.qOf ↥F w) ≃ₐ[ℚ_[A.qOf ↥F w]] PadicAlgCl (A.qOf ↥F w) from τ) y := by
    intro τ y
    rw [A.coe_actImg_smul, hequiv, A.apply_Φ₂_symm]

  have hbase₂ : ExtCitation.LocalLevel.IsBase (A.qOf ↥F w) (A.Limg ↥F w Φ hΦc) ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) ⊥ := by
    refine ⟨bot_le, fun y => ⟨fun hy g => ?_, fun hy => ?_⟩⟩
    · obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 hy
      have : y = algebraMap ℚ_[A.qOf ↥F w] (A.Limg ↥F w Φ hΦc) c := Subtype.ext hc.symm
      rw [this, hG₂]
    · have hfixΩ : ∀ τ : PadicAlgCl (A.qOf ↥F w) ≃ₐ[ℚ_[A.qOf ↥F w]] PadicAlgCl (A.qOf ↥F w), τ (y : PadicAlgCl (A.qOf ↥F w)) = y := by
        intro τ
        have := hact₂ τ y
        rw [hy (π τ)] at this
        exact this.symm
      obtain ⟨c, hc⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (y : PadicAlgCl (A.qOf ↥F w))).2 hfixΩ
      exact IntermediateField.mem_bot.2 ⟨c, hc⟩

  have hsolv := ExtCitation.LocalLevel.isSolvable_of_faithfulSMul_of_padic (A.qOf ↥F w) (A.Limg ↥F w Φ hΦc)
    ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) hG₂
  obtain ⟨u₂, hu₂, -⟩ := ExtCitation.LocalLevel.existsUnique_isLocalFundamentalClass (A.qOf ↥F w) (A.Limg ↥F w Φ hΦc)
    ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) hG₂ hcompat₂ hsolv ⊥ hbase₂

  have hUsymm : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (v : (↥(A.Limg ↥F w Φ hΦc))ˣ),
      Units.map ((A.Φ₂ ↥F w Φ hΦc).symm : A.Limg ↥F w Φ hΦc →* w.adicCompletion ↥F) (g • v) =
        g • Units.map ((A.Φ₂ ↥F w Φ hΦc).symm : A.Limg ↥F w Φ hΦc →* w.adicCompletion ↥F) v := by
    intro g v; apply Units.ext; exact A.Φ₂_symm_smul ↥F w ℚ Φ hΦc g (v : A.Limg ↥F w Φ hΦc)
  have hU : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (v : (w.adicCompletion ↥F)ˣ),
      Units.map ((A.Φ₂ ↥F w Φ hΦc) : w.adicCompletion ↥F →* A.Limg ↥F w Φ hΦc) (g • v) =
        g • Units.map ((A.Φ₂ ↥F w Φ hΦc) : w.adicCompletion ↥F →* A.Limg ↥F w Φ hΦc) v := by
    intro g v; apply Units.ext; exact A.Φ₂_smul ↥F w ℚ Φ hΦc g (v : w.adicCompletion ↥F)
  let θ₂ := A.repHom (Units.map ((A.Φ₂ ↥F w Φ hΦc).symm : A.Limg ↥F w Φ hΦc →* w.adicCompletion ↥F)) hUsymm
  let ΦU := A.repHom (Units.map ((A.Φ₂ ↥F w Φ hΦc) : w.adicCompletion ↥F →* A.Limg ↥F w Φ hΦc)) hU
  have hθ₂ : ∀ v : (↥(A.Limg ↥F w Φ hΦc))ˣ, ((Additive.toMul (θ₂.hom (Additive.ofMul v)) : (w.adicCompletion ↥F)ˣ) : w.adicCompletion ↥F) =
      (A.Φ₂ ↥F w Φ hΦc).toRingEquiv.symm (v : A.Limg ↥F w Φ hΦc) := fun v => rfl
  haveI : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) L' := by
    refine ⟨fun {a b} h => ?_⟩
    haveI := A.faithful_Kw ↥F w ℚ
    apply FaithfulSMul.eq_of_smul_eq_smul (α := w.adicCompletion ↥F)
    intro y
    apply Φ'.injective
    rw [hΦ', hΦ', h]
  have h92 := NumberField.PlaceDecomp.map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion ℚ ↥F w
    (A.qOf ↥F w) hqw L' Φ' hfix' hcompat' hΦ' K₀ hK₀ θ' hθ' u' hu'
    (A.qOf ↥F w) hqw (A.Limg ↥F w Φ hΦc) (A.Φ₂ ↥F w Φ hΦc).toRingEquiv hG₂ hcompat₂
    (fun g y => A.Φ₂_smul ↥F w ℚ Φ hΦc g y) ⊥ hbase₂ θ₂ hθ₂ u₂ hu₂

  let x₂ := (mapCocycles₂ (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) ΦU) x
  have hcomp : θ₂ ≫ ΦU = 𝟙 _ := by
    have hround : ∀ u : (↥(A.Limg ↥F w Φ hΦc))ˣ,
        Units.map ((A.Φ₂ ↥F w Φ hΦc) : w.adicCompletion ↥F →* A.Limg ↥F w Φ hΦc)
          (Units.map ((A.Φ₂ ↥F w Φ hΦc).symm : A.Limg ↥F w Φ hΦc →* w.adicCompletion ↥F) u) = u :=
      fun u => Units.ext ((A.Φ₂ ↥F w Φ hΦc).apply_symm_apply (u : A.Limg ↥F w Φ hΦc))
    apply Rep.hom_ext
    ext v
    change Additive.ofMul (Units.map ((A.Φ₂ ↥F w Φ hΦc) : w.adicCompletion ↥F →* A.Limg ↥F w Φ hΦc)
      (Units.map ((A.Φ₂ ↥F w Φ hΦc).symm : A.Limg ↥F w Φ hΦc →* w.adicCompletion ↥F) (Additive.toMul v))) = v
    rw [hround, ofMul_toMul]
  have hx₂ : (H2π (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥(A.Limg ↥F w Φ hΦc))ˣ)).hom x₂ =
      m • ((Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) / p) • u₂) := by
    have e1 := groupCohomology.H2π_comp_map_apply (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) ΦU x

    have e2 : (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) ΦU 2).hom
        ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) θ₂ 2).hom u₂) = u₂ := by
      have := groupCohomology.map_id_comp θ₂ ΦU 2
      rw [hcomp, groupCohomology.map_id] at this
      have := congrArg (fun f => (ModuleCat.Hom.hom f) u₂) this
      simpa using this.symm
    change (H2π _).hom x₂ = _
    rw [← e1, hx, hz, map_zsmul, map_nsmul, h92, e2]
  have hX₂ : ∀ g h : primeLocalGaloisGroup ⟨A.qOf ↥F w, hqn⟩,
      ((Additive.toMul ((X : primeLocalGaloisGroup ⟨A.qOf ↥F w, hqn⟩ × primeLocalGaloisGroup ⟨A.qOf ↥F w, hqn⟩ →
        (show Rep ℤ (primeLocalGaloisGroup ⟨A.qOf ↥F w, hqn⟩) from Rep.ofAlgebraAutOnUnits ℚ_[A.qOf ↥F w] (PadicAlgCl (A.qOf ↥F w)))) (g, h)) :
          (PadicAlgCl (A.qOf ↥F w))ˣ) : PadicAlgCl (A.qOf ↥F w)) =
        (((Additive.toMul (x₂ (π g, π h)) : (↥(A.Limg ↥F w Φ hΦc))ˣ) : A.Limg ↥F w Φ hΦc) : PadicAlgCl (A.qOf ↥F w)) := by
    intro g h
    have h1 := congrArg Units.val (hX g h)
    rw [Units.coe_map] at h1
    exact h1.trans rfl

  have hlev : ∃ F₁ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₁ ∧
      ∀ τ : primeLocalGaloisGroup ⟨A.qOf ↥F w, hqn⟩, localGaloisToGlobal (A.qOf ↥F w)
        (show PadicAlgCl (A.qOf ↥F w) ≃ₐ[ℚ_[A.qOf ↥F w]] PadicAlgCl (A.qOf ↥F w) from τ) ∈ F₁.fixingSubgroup → π τ = 1 := by
    refine ⟨F.map σ.toAlgHom, IntermediateField.finiteDimensional_map (E := F) σ.toAlgHom, fun τ hτ => ?_⟩
    apply Subtype.ext
    rw [hπ τ, OneMemClass.coe_one]
    change AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal (A.qOf ↥F w)
      (show PadicAlgCl (A.qOf ↥F w) ≃ₐ[ℚ_[A.qOf ↥F w]] PadicAlgCl (A.qOf ↥F w) from τ) * σ) = 1
    refine AlgEquiv.ext fun y => ?_
    apply (algebraMap ↥F (AlgebraicClosure ℚ)).injective
    change algebraMap ↥F (AlgebraicClosure ℚ) (((σ⁻¹ * localGaloisToGlobal (A.qOf ↥F w)
      (show PadicAlgCl (A.qOf ↥F w) ≃ₐ[ℚ_[A.qOf ↥F w]] PadicAlgCl (A.qOf ↥F w) from τ) * σ).restrictNormal ↥F) y) =
      algebraMap ↥F (AlgebraicClosure ℚ) ((1 : ↥F ≃ₐ[ℚ] ↥F) y)
    rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.one_apply, AlgEquiv.mul_apply, AlgEquiv.mul_apply]
    have hyF : σ (algebraMap ↥F (AlgebraicClosure ℚ) y) ∈ F.map σ.toAlgHom :=
      ⟨y, y.2, rfl⟩
    rw [(IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ _ hyF]
    exact (σ.symm_apply_apply _)
  haveI hgal : IsGalois ℚ_[A.qOf ↥F w] (A.Limg ↥F w Φ hΦc) := by
    apply IsGalois.of_fixedField_eq_bot
    rw [eq_bot_iff]
    intro y hy
    let gAut : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) → (A.Limg ↥F w Φ hΦc ≃ₐ[ℚ_[A.qOf ↥F w]] A.Limg ↥F w Φ hΦc) :=
      fun g => AlgEquiv.ofRingEquiv (f := MulSemiringAction.toRingEquiv _ (A.Limg ↥F w Φ hΦc) g) (hG₂ g)
    have hyfix : ∀ g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w), g • y = y :=
      fun g => (IntermediateField.mem_fixedField_iff _ _).1 hy (gAut g) (Subgroup.mem_top _)
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 ((hbase₂.mem_iff y).2 hyfix)
    exact IntermediateField.mem_bot.2 ⟨c, Subtype.ext hc⟩
  refine ⟨A.Limg ↥F w Φ hΦc, inferInstance, act, hfaith, actU, hgal, u₂, x₂, ?_⟩
  exact ⟨hG₂, hcompat₂, hact₂, hbase₂, hu₂, hx₂, hX₂, hlev⟩

end F2a
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_inflate_sub_unitsInflate2_carryFun_mem_levelCoboundaries2.F2a.A P2MW.S_NumberField_PlaceDecomp_inflate_sub_unitsInflate2_carryFun_mem_levelCoboundaries2.F2a"

theorem solution
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) [Fact ((q : ℕ)).Prime]
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) :
    ∀ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (w : HeightOneSpectrum (𝓞 ↥F))
    (hpD : p ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))

    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
    (_ : ∀ x : ↥F, Φ (algebraMap ↥F (w.adicCompletion ↥F) x) = padicEmbedding q (σ (x : AlgebraicClosure ℚ)))
    (_ : Continuous Φ)
    (π : primeLocalGaloisGroup q →* ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))
    (_ : ∀ τ : primeLocalGaloisGroup q, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ))
    (_ : Function.Surjective π)
    (_ : ∀ (τ : primeLocalGaloisGroup q) (x : w.adicCompletion ↥F),
      Φ (π τ • x) = (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (Φ x))

    (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L')ˣ]
    (Φ' : w.adicCompletion ↥F ≃+* L')
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : w.adicCompletion ↥F), Φ' (g • x) = g • Φ' x)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
    (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) K₀)
    (θ' : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L')ˣ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
    (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ'.hom (Additive.ofMul v)) : (w.adicCompletion ↥F)ˣ) : w.adicCompletion ↥F) = Φ'.symm (v : L'))
    (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L')ˣ))
    (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) K₀ u')

    (m : ℤ) (z : groupCohomology (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) 2)
    (_ : z = m • ((Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) / p) •
      (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) θ' 2).hom u'))
    (x : cocycles₂ (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)) (_ : (H2π (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)).hom x = z)
    (X : levelCocycles₂ (primeLocalToGlobal q) (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
    (_ : ∀ g h : primeLocalGaloisGroup q, Additive.toMul ((X : primeLocalGaloisGroup q × primeLocalGaloisGroup q → (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) (g, h)) =
      Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q) (Additive.toMul ((x : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) × ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) → Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) (π g, π h))))

    (φ : (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}) ≃ₐ[ℚ_[q]] (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}))
    (hs : ∀ σ, σ ∈ Subgroup.zpowers φ) (hfin : IsOfFinOrder φ)
    (_ : ∀ x : (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}), (x : PadicAlgCl q) ^ ((q : ℕ) ^ p - 1) = 1 → (φ x : PadicAlgCl q) = (x : PadicAlgCl q) ^ (q : ℕ))
    (α : ((IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}))ˣ)
    (_ : ((α : (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1})) : PadicAlgCl q) = algebraMap ℚ_[q] (PadicAlgCl q) ((q : ℚ_[q]) ^ m))
    (_ : Normal ℚ_[q] (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1})),
    (fun g : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) =>
        (show Additive (PadicAlgCl q)ˣ from
          (X : primeLocalGaloisGroup q × primeLocalGaloisGroup q → (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) g))
      - unitsInflate₂ (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1})
          (carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1})) (Additive.ofMul α))
      ∈ levelCoboundaries₂ (localGaloisToGlobal q) (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) := by
  intro F _nf _gal w hpD σ Φ hΦ hΦc π hπ hπs hequiv L' _fdL' _msaL' _mdmaL' Φ' hfix' hcompat' hΦ' K₀ _fdK₀ hK₀ θ' hθ' u' hu'
    m z hz x hx X hX φ hs hfin hφ α hα _normal
  obtain ⟨L₂, _fd, _msa, _faith, _mdma, _gal₂, u₂, x₂, hG₂, hcompat₂, hact₂, hbase₂, hu₂, hx₂, hX₂, hlev₂⟩ :=
    F2a.stageA q F w hpD σ Φ hΦ hΦc π hπ hπs hequiv L' Φ' hfix' hcompat' hΦ' K₀ hK₀ θ' hθ' u' hu' m z hz x hx X hX

  have hαfix : (Rep.ofAlgebraAutOnUnits ℚ_[q] (F2a.L0 q p)).ρ φ (Additive.ofMul α) = Additive.ofMul α := by
    have hαL : (α : F2a.L0 q p) = algebraMap ℚ_[q] (F2a.L0 q p) ((q : ℚ_[q]) ^ m) := Subtype.ext hα
    have hφα : φ (α : F2a.L0 q p) = α := by rw [hαL, AlgEquiv.commutes]
    change Additive.ofMul (φ • α) = Additive.ofMul α
    congr 1
    exact Units.ext hφα
  have hc := groupCohomology.carryFun_mem_cocycles2 φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] (F2a.L0 q p)) (Additive.ofMul α) hαfix
  haveI := _normal
  refine F2a.stageC q p L₂ (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) hG₂ hcompat₂ π hπs hact₂ hlev₂ x₂ X hX₂ φ hs hfin α hc ?_
  intro M _ _ hL₂M hL₀M r₂ hr₂s hr₂ ι₂ hι₂ r₀ hr₀s hr₀ ι₀ hι₀
  rw [hx₂]
  exact F2a.stageB q p L₂ (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) hG₂ hcompat₂ hbase₂ u₂ hu₂ hpD m φ hs hfin hφ α hα hc
    M hL₂M hL₀M r₂ hr₂s hr₂ ι₂ hι₂ r₀ hr₀s hr₀ ι₀ hι₀

end S_NumberField_PlaceDecomp_inflate_sub_unitsInflate2_carryFun_mem_levelCoboundaries2
end P2MW
export P2MW.S_NumberField_PlaceDecomp_inflate_sub_unitsInflate2_carryFun_mem_levelCoboundaries2 (solution)
