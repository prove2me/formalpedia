-- Prove2me | solution 1 for ModularCurve.ComplexPlaceDictionaryOf.restrictAlong_pt_qExpand
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/cc089af5-5124-5b1e-b7c9-d260088d028b

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_restrictAlong_pt_qExpand

set_option autoImplicit false

noncomputable section

p2m_open "UpperHalfPlane ModularForm ConjAct Filter ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_restrictAlong_pt_qExpand.ModularCurve AlgebraicCurve"
open scoped MatrixGroups ConjAct Pointwise Topology Manifold

namespace ModularCurve
p2m_export "ModularCurve" "realizeOf realizeOf_of_not ComplexPlaceDictionaryOf laurentBaseChange ComplexPlaceDictionary qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd realizeOf_eq_div"
namespace RestrictAlongPtQExpand
p2m_open "ModularCurve"

def restrict {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ) {k : ℤ} (f : ModularForm Γ k)
    [Γ'.HasDetPlusMinusOne] : ModularForm Γ' k where
  toSlashInvariantForm := ⟨f, fun γ hγ => SlashInvariantForm.slash_action_eqn f γ (hle hγ)⟩
  holo' := f.holo'
  bdd_at_cusps' := fun hc => f.bdd_at_cusps' (hc.mono hle)

@[scoped simp] theorem coe_restrict {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ) {k : ℤ}
    (f : ModularForm Γ k) [Γ'.HasDetPlusMinusOne] :
    ((restrict hle f : ModularForm Γ' k) : ℍ → ℂ) = f := rfl

theorem coe_le_conj_of_le_conjGL {Γ Γ' : Subgroup SL(2, ℤ)} {g : GL (Fin 2) ℝ}
    (h : Γ' ≤ CongruenceSubgroup.conjGL Γ g) :
    ((Γ' : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      toConjAct g⁻¹ • ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  change Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ' ≤ _
  rw [Subgroup.map_le_iff_le_comap]
  exact h

variable (ℓ : ℕ)

def shift {Γ Γ' : Subgroup SL(2, ℤ)}
    (hΓ' : Γ' ≤ CongruenceSubgroup.conjGL Γ (heckeDiagMatrix ℓ)) {k : ℤ} (g : ModularForm Γ k) :
    ModularForm Γ' k :=
  haveI : ((Γ' : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).HasDetPlusMinusOne := inferInstance
  restrict (coe_le_conj_of_le_conjGL hΓ') (ModularForm.translate g (heckeDiagMatrix ℓ))

theorem shift_apply [NeZero ℓ] {Γ Γ' : Subgroup SL(2, ℤ)}
    (hΓ' : Γ' ≤ CongruenceSubgroup.conjGL Γ (heckeDiagMatrix ℓ)) {k : ℤ} (g : ModularForm Γ k)
    (τ : ℍ) : shift ℓ hΓ' g τ = (ℓ : ℂ) ^ (k - 1) * g (heckeDiagMatrix ℓ • τ) := by
  rw [← slash_heckeDiagMatrix_apply k (NeZero.ne ℓ)]
  rfl

variable {ℓ}

theorem one_mem_strictPeriods {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples 1

theorem qParam_heckeDiag_smul (hℓ : ℓ ≠ 0) (τ : ℍ) :
    Function.Periodic.qParam 1 ((heckeDiagMatrix ℓ • τ : ℍ) : ℂ) =
      Function.Periodic.qParam 1 (τ : ℂ) ^ ℓ := by
  simp only [Function.Periodic.qParam]
  rw [coe_heckeDiagMatrix_smul hℓ, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

def shiftCoeff (ℓ : ℕ) (k : ℤ) (a : ℕ → ℂ) (m : ℕ) : ℂ :=
  if ℓ ∣ m then (ℓ : ℂ) ^ (k - 1) * a (m / ℓ) else 0

theorem hasSum_shift [NeZero ℓ] {Γ Γ' : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ)
    (hΓ' : Γ' ≤ CongruenceSubgroup.conjGL Γ (heckeDiagMatrix ℓ)) {k : ℤ}
    (g : ModularForm Γ k) (τ : ℍ) :
    HasSum (fun m : ℕ => shiftCoeff ℓ k (fun n => (qExpansion 1 g).coeff n) m •
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (shift ℓ hΓ' g τ) := by
  have hℓ := NeZero.ne ℓ
  haveI : Fact (IsCusp OnePoint.infty ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods hT)⟩
  have h1 := hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex g (one_mem_strictPeriods hT))
    (ModularFormClass.holo g) (ModularFormClass.bdd_at_infty g) (heckeDiagMatrix ℓ • τ)
  rw [qParam_heckeDiag_smul hℓ] at h1
  have h2 := h1.mul_left ((ℓ : ℂ) ^ (k - 1))
  rw [shift_apply]
  have hinj : Function.Injective (fun n : ℕ => ℓ * n) := mul_right_injective₀ hℓ
  have hsupp : ∀ m ∉ Set.range (fun n : ℕ => ℓ * n),
      shiftCoeff ℓ k (fun n => (qExpansion 1 g).coeff n) m •
        Function.Periodic.qParam 1 (τ : ℂ) ^ m = 0 := by
    intro m hm
    have hd : ¬ ℓ ∣ m := fun ⟨n, hn⟩ => hm ⟨n, hn.symm⟩
    simp [shiftCoeff, hd]
  refine (hinj.hasSum_iff hsupp).mp ?_
  convert h2 using 1 <;> try rfl
  ext n
  simp only [Function.comp_apply, shiftCoeff, dvd_mul_right, if_true,
    Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hℓ), smul_eq_mul, pow_mul]
  ring

theorem qExpansion_shift_coeff [NeZero ℓ] {Γ Γ' : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ)
    (hT' : ModularGroup.T ∈ Γ') (hΓ' : Γ' ≤ CongruenceSubgroup.conjGL Γ (heckeDiagMatrix ℓ))
    {k : ℤ} (g : ModularForm Γ k) (m : ℕ) :
    (qExpansion 1 (shift ℓ hΓ' g)).coeff m =
      shiftCoeff ℓ k (fun n => (qExpansion 1 g).coeff n) m :=
  (ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods hT')
    (f := shift ℓ hΓ' g) (hasSum_shift hT hΓ' g) m).symm

theorem coe_qExpansion_shift [NeZero ℓ] {Γ Γ' : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ)
    (hT' : ModularGroup.T ∈ Γ') (hΓ' : Γ' ≤ CongruenceSubgroup.conjGL Γ (heckeDiagMatrix ℓ))
    {k : ℤ} (g : ModularForm Γ k) :
    ((qExpansion 1 (shift ℓ hΓ' g) : PowerSeries ℂ) : LaurentSeries ℂ) =
      HahnSeries.C ((ℓ : ℂ) ^ (k - 1)) *
        ModularCurve.qExpand ℂ ℓ ((qExpansion 1 g : PowerSeries ℂ) : LaurentSeries ℂ) := by
  have hℓ := NeZero.ne ℓ
  rw [HahnSeries.C_mul_eq_smul]
  ext m
  rw [HahnSeries.coeff_smul, PowerSeries.coeff_coe, smul_eq_mul]
  by_cases hd : (ℓ : ℤ) ∣ m
  · obtain ⟨n, rfl⟩ := hd
    rw [ModularCurve.qExpand_coeff_mul, PowerSeries.coeff_coe]
    by_cases hn : n < 0
    · have : (ℓ : ℤ) * n < 0 := by
        have : (0 : ℤ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero hℓ
        nlinarith
      rw [if_pos this, if_pos hn, mul_zero]
    · have hn' : 0 ≤ n := le_of_not_gt hn
      have : ¬ (ℓ : ℤ) * n < 0 := not_lt.mpr (by positivity)
      rw [if_neg this, if_neg hn, qExpansion_shift_coeff hT hT' hΓ', shiftCoeff, Int.natAbs_mul,
        Int.natAbs_natCast, if_pos (dvd_mul_right _ _),
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hℓ)]
  · rw [ModularCurve.qExpand_coeff_of_not_dvd ℓ _ hd, mul_zero]
    split_ifs with hm
    · rfl
    · rw [qExpansion_shift_coeff hT hT' hΓ', shiftCoeff, if_neg]
      intro h
      apply hd
      have hm' : (m : ℤ) = (m.natAbs : ℕ) := (Int.natAbs_of_nonneg (le_of_not_gt hm)).symm
      rw [hm']
      exact_mod_cast h

theorem coe_eq_zero_iff {Γ : Subgroup SL(2, ℤ)} {k : ℤ} (f : ModularForm Γ k) :
    (f : ℍ → ℂ) = 0 ↔ f = 0 := by
  constructor
  · intro h
    exact DFunLike.coe_injective (h.trans (ModularForm.coe_zero).symm)
  · rintro rfl; rfl

theorem eventually_ne_zero {Γ : Subgroup SL(2, ℤ)} {k : ℤ} (f : ModularForm Γ k)
    (hf : f ≠ 0) (τ : ℍ) : ∀ᶠ w in 𝓝[≠] τ, (f : ℍ → ℂ) w ≠ 0 := by
  by_contra hcon
  have hfr : ∃ᶠ w in 𝓝[≠] τ, (f : ℍ → ℂ) w = 0 := by
    simpa [Filter.not_eventually] using hcon
  exact hf ((coe_eq_zero_iff f).mp (eq_zero_of_frequently (ModularFormClass.holo f) hfr))

variable (ℓ) in

theorem map_heckeDiag_smul_nhdsNE (τ : ℍ) :
    Filter.map (fun z : ℍ => heckeDiagMatrix ℓ • z) (𝓝[≠] τ) = 𝓝[≠] (heckeDiagMatrix ℓ • τ) :=
  (Homeomorph.smul (heckeDiagMatrix ℓ) : ℍ ≃ₜ ℍ).map_punctured_nhds_eq τ

theorem map_coe_nhdsNE (τ : ℍ) :
    Filter.map ((↑) : ℍ → ℂ) (𝓝[≠] τ) = 𝓝[≠] (τ : ℂ) := by
  have h := isOpenEmbedding_coe.map_nhdsWithin_preimage_eq ({(τ : ℂ)}ᶜ) τ
  have hpre : ((↑) : ℍ → ℂ) ⁻¹' ({(τ : ℂ)}ᶜ : Set ℂ) = ({τ}ᶜ : Set ℍ) := by
    ext w
    simp
  rwa [hpre] at h

theorem eventually_nhdsNE_coe_iff {p : ℍ → Prop} {τ : ℍ} :
    (∀ᶠ z in 𝓝[≠] (τ : ℂ), p (ofComplex z)) ↔ ∀ᶠ w in 𝓝[≠] τ, p w := by
  rw [← map_coe_nhdsNE, Filter.eventually_map]
  simp only [ofComplex_apply]

theorem isBoundedUnder_congr {α : Type*} {l : Filter α} {u v : α → ℝ} (h : u =ᶠ[l] v) :
    IsBoundedUnder (· ≤ ·) l u ↔ IsBoundedUnder (· ≤ ·) l v :=
  ⟨fun hu => hu.mono_le h.symm.le, fun hv => hv.mono_le h.le⟩

theorem mem_restrictAlong_iff {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (x : F) :
    x ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ x ∈ w.toValuationSubring :=
  Iff.rfl

theorem exists_presentation {Γ : Subgroup SL(2, ℤ)} {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}
    (D : ComplexPlaceDictionaryOf Γ F₀) (x : laurentBaseChange ℂ F₀) (hx : x ≠ 0) :
    ∃ (k : ℤ) (g h : ModularForm Γ k), h ≠ 0 ∧
      (x : LaurentSeries ℂ) * ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
        ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
  classical
  by_contra hcon
  push Not at hcon
  have h0 : ∀ z : ℍ, realizeOf Γ (x : LaurentSeries ℂ) z = 0 := by
    intro z
    apply realizeOf_of_not
    rintro ⟨⟨k, g, h⟩, hz, hxh⟩
    refine hcon k g h ?_ hxh
    rintro rfl
    exact hz (ModularForm.zero_apply z)
  have hA := D.meromorphicOrderAt_realizeOf UpperHalfPlane.I x hx
  have htop : meromorphicOrderAt
      (fun z : ℂ => realizeOf Γ (x : LaurentSeries ℂ) (ofComplex z)) ((UpperHalfPlane.I : ℍ) : ℂ) = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (Filter.Eventually.of_forall fun z => h0 _)
  rw [htop] at hA
  exact WithTop.top_ne_coe hA

variable (ℓ) in

theorem realizeOf_qExpand_eventuallyEq [NeZero ℓ] {Γ Γ' : Subgroup SL(2, ℤ)}
    (hT : ModularGroup.T ∈ Γ) (hT' : ModularGroup.T ∈ Γ')
    (hΓ' : Γ' ≤ CongruenceSubgroup.conjGL Γ (heckeDiagMatrix ℓ))
    {k : ℤ} (g h : ModularForm Γ k) (hh : h ≠ 0) (x : LaurentSeries ℂ)
    (hgh : x * ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (τ : ℍ) :
    (fun z : ℍ => realizeOf Γ' (qExpand ℂ ℓ x) z) =ᶠ[𝓝[≠] τ]
      fun z : ℍ => realizeOf Γ x (heckeDiagMatrix ℓ • z) := by
  have hℓ : (ℓ : ℂ) ^ (k - 1) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast NeZero.ne ℓ)

  have hgh' : qExpand ℂ ℓ x *
      ((qExpansion 1 (shift ℓ hΓ' h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
        ((qExpansion 1 (shift ℓ hΓ' g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
    rw [coe_qExpansion_shift hT hT' hΓ', coe_qExpansion_shift hT hT' hΓ', mul_left_comm, ← map_mul,
      hgh]

  have hev : ∀ᶠ z in 𝓝[≠] τ, (h : ℍ → ℂ) (heckeDiagMatrix ℓ • z) ≠ 0 := by
    have := eventually_ne_zero h hh (heckeDiagMatrix ℓ • τ)
    rw [← map_heckeDiag_smul_nhdsNE ℓ τ, Filter.eventually_map] at this
    exact this
  filter_upwards [hev] with z hz
  have hz' : (shift ℓ hΓ' h : ℍ → ℂ) z ≠ 0 := by
    rw [shift_apply]; exact mul_ne_zero hℓ hz
  rw [realizeOf_eq_div Γ' hT' (shift ℓ hΓ' g) (shift ℓ hΓ' h) _ hgh' z hz',
    realizeOf_eq_div Γ hT g h x hgh _ hz, shift_apply, shift_apply, mul_div_mul_left _ _ hℓ]

end ModularCurve.RestrictAlongPtQExpand
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_restrictAlong_pt_qExpand.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_restrictAlong_pt_qExpand.ModularCurve.RestrictAlongPtQExpand"
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_restrictAlong_pt_qExpand.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_restrictAlong_pt_qExpand.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_restrictAlong_pt_qExpand.ModularCurve.RestrictAlongPtQExpand"

open UpperHalfPlane _root_.ModularCurve _root_.P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_restrictAlong_pt_qExpand.ModularCurve AlgebraicCurve ModularCurve.RestrictAlongPtQExpand Filter in
open scoped Topology MatrixGroups in
theorem solution
    (Γ Γ' : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ) (hT' : ModularGroup.T ∈ Γ')
    (ℓ : ℕ) [NeZero ℓ] (hΓ' : Γ' ≤ CongruenceSubgroup.conjGL Γ (ModularForm.heckeDiagMatrix ℓ))
    (F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ))
    (D : ModularCurve.ComplexPlaceDictionaryOf Γ F₀) (D' : ModularCurve.ComplexPlaceDictionaryOf Γ' F₁)
    (β : ModularCurve.laurentBaseChange ℂ F₀ →ₐ[ℂ] ModularCurve.laurentBaseChange ℂ F₁)
    (hβq : ∀ x : ModularCurve.laurentBaseChange ℂ F₀,
      ((β x : ModularCurve.laurentBaseChange ℂ F₁) : LaurentSeries ℂ) =
        ModularCurve.qExpand ℂ ℓ (x : LaurentSeries ℂ))
    (hβ : β.toRingHom.IsIntegral) (τ : UpperHalfPlane) :
    (D'.pt τ).restrictAlong β hβ = D.pt (ModularForm.heckeDiagMatrix ℓ • τ) ∧
      D'.ramification τ * (D'.pt τ).ramificationIndexAlong β =
        D.ramification (ModularForm.heckeDiagMatrix ℓ • τ) := by

  have h1 : (D'.pt τ).restrictAlong β hβ = D.pt (ModularForm.heckeDiagMatrix ℓ • τ) := by
    apply Place.ext
    ext x
    by_cases hx0 : x = 0
    · subst hx0
      exact iff_of_true (zero_mem _) (zero_mem _)
    obtain ⟨k, g, h, hh, hgh⟩ := exists_presentation D x hx0
    rw [mem_restrictAlong_iff, D'.mem_pt_iff, D.mem_pt_iff, hβq]
    have hq : (fun z : ℍ => ‖realizeOf Γ' (qExpand ℂ ℓ (x : LaurentSeries ℂ)) z‖) =ᶠ[𝓝[≠] τ]
        fun z : ℍ => ‖realizeOf Γ (x : LaurentSeries ℂ) (ModularForm.heckeDiagMatrix ℓ • z)‖ :=
      (realizeOf_qExpand_eventuallyEq ℓ hT hT' hΓ' g h hh (x : LaurentSeries ℂ) hgh τ).fun_comp (‖·‖)
    rw [isBoundedUnder_congr hq, ← map_heckeDiag_smul_nhdsNE ℓ τ]
    exact Filter.isBoundedUnder_map_iff.symm
  refine ⟨h1, ?_⟩

  set w := ModularForm.heckeDiagMatrix ℓ • τ with hw
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (D.pt w).toValuationSubring
  set x : laurentBaseChange ℂ F₀ := (π : laurentBaseChange ℂ F₀) with hx
  have hordx : (D.pt w).ord x = 1 := (D.pt w).ord_coe_irreducible hπ
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at hordx
    exact zero_ne_one hordx
  have hβx0 : β x ≠ 0 := (map_ne_zero _).mpr hx0
  obtain ⟨k, g, h, hh, hgh⟩ := exists_presentation D x hx0

  have hA := D'.meromorphicOrderAt_realizeOf τ (β x) hβx0
  rw [Place.ord_restrictAlong β hβ, h1, hordx, mul_one] at hA

  have hB := D.meromorphicOrderAt_realizeOf w x hx0
  rw [hordx, mul_one] at hB

  have hev : (fun z : ℂ => realizeOf Γ' ((β x : _) : LaurentSeries ℂ)
      (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
        fun z : ℂ => realizeOf Γ (x : LaurentSeries ℂ)
          (ModularForm.heckeDiagMatrix ℓ • ofComplex z) := by
    rw [hβq]
    exact (eventually_nhdsNE_coe_iff (p := fun v : ℍ =>
      realizeOf Γ' (qExpand ℂ ℓ (x : LaurentSeries ℂ)) v =
        realizeOf Γ (x : LaurentSeries ℂ) (ModularForm.heckeDiagMatrix ℓ • v))).mpr
      (realizeOf_qExpand_eventuallyEq ℓ hT hT' hΓ' g h hh (x : LaurentSeries ℂ) hgh τ)
  have hcomp := UpperHalfPlane.meromorphicOrderAt_comp_smul
    (f := fun v : ℍ => realizeOf Γ (x : LaurentSeries ℂ) v) (τ := τ)
    (g := ModularForm.heckeDiagMatrix ℓ)
    (by rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact ModularForm.det_heckeDiagMatrix_pos ℓ)
  rw [meromorphicOrderAt_congr hev, hcomp, ← hw, hB] at hA
  have := WithTop.coe_injective hA
  exact_mod_cast this.symm

end S_ModularCurve_ComplexPlaceDictionaryOf_restrictAlong_pt_qExpand
end P2MW
export P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_restrictAlong_pt_qExpand (solution)
