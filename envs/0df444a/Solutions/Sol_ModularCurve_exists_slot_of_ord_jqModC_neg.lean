-- Prove2me | solution 1 for ModularCurve.exists_slot_of_ord_jqModC_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/94e94b58-0254-5c71-ba68-967ae44eaf6e

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_ModularCurve_minpoly_jqNModC_map_eq_prod_slots
import Theorems.Thm_ModularCurve_finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_StarBank_starBank
import Theorems.Thm_ModularCurve_jqNModC_prime_not_mem_adjoin_of_charZero
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_le_finrank
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_pos
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_subsingleton_setOf_forall_ne_ofHeightOneSpectrum
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_algHom_laurentSeries
import Theorems.Thm_ModularCurve_order_qExpand
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_slot_of_ord_jqModC_neg
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X"
p2m_attr_erase "simp" "ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply HahnSeries.ramScale_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 320000
set_option maxHeartbeats 3200000

noncomputable section

open ModularCurve AlgebraicCurve Polynomial IntermediateField

namespace CuspCountModC

section Numerics

def slotFinset (N : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  N.divisors.sigma fun a => (Finset.range (N / a)).filter fun b => Nat.gcd (Nat.gcd a b) (N / a) = 1

theorem mem_slotFinset {N : ℕ} [NeZero N] (s : Σ _ : ℕ, ℕ) :
    s ∈ slotFinset N ↔ s.1 ∣ N ∧ s.2 < N / s.1 ∧ Nat.gcd (Nat.gcd s.1 s.2) (N / s.1) = 1 := by
  cases s with
  | mk a b =>
    simp only [slotFinset, Finset.mem_sigma, Nat.mem_divisors, Finset.mem_filter,
      Finset.mem_range, and_assoc]
    exact ⟨fun ⟨h1, _, h2, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, NeZero.ne N, h2, h3⟩⟩

theorem slot_cond_iff (a b d : ℕ) :
    Nat.gcd (Nat.gcd a b) d = 1 ↔ Nat.gcd b (Nat.gcd a d) = 1 := by
  rw [Nat.gcd_assoc, Nat.gcd_comm b d, ← Nat.gcd_assoc, Nat.gcd_comm]

theorem slot_cond_congr (a d : ℕ) {b b' : ℕ} (h : b ≡ b' [MOD Nat.gcd a d]) :
    Nat.gcd (Nat.gcd a b) d = 1 ↔ Nat.gcd (Nat.gcd a b') d = 1 := by
  rw [slot_cond_iff, slot_cond_iff, Nat.gcd_comm b, Nat.gcd_comm b', Nat.gcd_rec,
    Nat.gcd_rec (Nat.gcd a d) b', show b % Nat.gcd a d = b' % Nat.gcd a d from h]

theorem card_range_filter_modEq {g d : ℕ} (hg : 0 < g) (hgd : g ∣ d) (b : ℕ) :
    ((Finset.range d).filter (· ≡ b [MOD g])).card = d / g := by
  obtain ⟨c, rfl⟩ := hgd
  have h := Nat.count_modEq_card (b := g * c) (r := g) hg b
  rw [Nat.count_eq_card_filter_range] at h
  rw [Nat.mul_mod_right] at h
  simpa using h

theorem card_slotFibre (N : ℕ) [NeZero N] {α : Type*} [DecidableEq α] (P : (Σ _ : ℕ, ℕ) → α)
    (hP : ∀ s ∈ slotFinset N, ∀ s' ∈ slotFinset N,
      P s = P s' ↔ s.1 = s'.1 ∧ s.2 ≡ s'.2 [MOD Nat.gcd s.1 (N / s.1)])
    (s₀ : Σ _ : ℕ, ℕ) (hs₀ : s₀ ∈ slotFinset N) :
    ((slotFinset N).filter fun s => P s = P s₀).card = N / s₀.1 / Nat.gcd s₀.1 (N / s₀.1) := by
  set g₀ := Nat.gcd s₀.1 (N / s₀.1) with hg₀
  have hs₀' := (mem_slotFinset s₀).mp hs₀
  have ha0 : s₀.1 ≠ 0 := fun h => NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ hs₀'.1))
  have hg₀pos : 0 < g₀ := Nat.pos_of_ne_zero (Nat.gcd_ne_zero_left ha0)
  have hg₀dvd : g₀ ∣ N / s₀.1 := Nat.gcd_dvd_right _ _
  refine (Finset.card_nbij (fun b => (⟨s₀.1, b⟩ : Σ _ : ℕ, ℕ))
    (s := (Finset.range (N / s₀.1)).filter (· ≡ s₀.2 [MOD g₀]))
    (t := (slotFinset N).filter fun s => P s = P s₀) ?_ ?_ ?_).symm.trans
    (card_range_filter_modEq hg₀pos hg₀dvd s₀.2)
  · intro b hb
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hb
    have hmem : (⟨s₀.1, b⟩ : Σ _ : ℕ, ℕ) ∈ slotFinset N := by
      rw [mem_slotFinset]
      exact ⟨hs₀'.1, hb.1, (slot_cond_congr s₀.1 (N / s₀.1) hb.2).mpr hs₀'.2.2⟩
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨hmem, (hP _ hmem _ hs₀).mpr ⟨rfl, hb.2⟩⟩
  · intro b _ b' _ h
    simpa using h
  · intro s hs
    rw [Finset.mem_coe, Finset.mem_filter] at hs
    obtain ⟨ha, hb⟩ := (hP _ hs.1 _ hs₀).mp hs.2
    have hs' := (mem_slotFinset s).mp hs.1
    refine ⟨s.2, ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, ?_⟩
      · have := hs'.2.1; rwa [ha] at this
      · show s.2 ≡ s₀.2 [MOD Nat.gcd s₀.1 (N / s₀.1)]
        rw [← ha]; exact hb
    · cases s with
      | mk a b => simp only at ha ⊢; subst ha; rfl

def labels (N : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  N.divisors.sigma fun a => {b ∈ Finset.range (Nat.gcd a (N / a)) | (Nat.gcd a (N / a)).Coprime b}

theorem mem_labels {N : ℕ} [NeZero N] (s : Σ _ : ℕ, ℕ) :
    s ∈ labels N ↔ s.1 ∣ N ∧ s.2 < Nat.gcd s.1 (N / s.1) ∧ (Nat.gcd s.1 (N / s.1)).Coprime s.2 := by
  cases s with
  | mk a b =>
    simp only [labels, Finset.mem_sigma, Nat.mem_divisors, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun ⟨⟨h1, _⟩, h2, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, NeZero.ne N⟩, h2, h3⟩⟩

theorem card_labels (N : ℕ) : (labels N).card = cuspCount N := by
  rw [labels, Finset.card_sigma, cuspCount]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Nat.totient_eq_card_coprime]

theorem gcd_gcd_swap (a b c : ℕ) : Nat.gcd (Nat.gcd a b) c = Nat.gcd (Nat.gcd a c) b := by
  rw [Nat.gcd_assoc, Nat.gcd_comm b c, ← Nat.gcd_assoc]

end Numerics

section Laurent

variable (K : Type*) [Field K]

theorem jqModC_ne_zero : jqModC K ≠ 0 := by
  intro h
  have := order_jqModC K
  rw [h, HahnSeries.order_zero] at this
  exact absurd this (by norm_num)

theorem order_eq_of_coeff {x : LaurentSeries K} {m : ℤ} (h1 : x.coeff m ≠ 0)
    (h2 : ∀ i < m, x.coeff i = 0) : x.order = m := by
  have hx : x ≠ 0 := fun h => h1 (by rw [h]; rfl)
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1) ?_
  by_contra! h
  exact hx (HahnSeries.coeff_order_eq_zero.mp (h2 _ h))

theorem order_qTwist (v : Kˣ) {f : LaurentSeries K} (hf : f ≠ 0) : (qTwist v f).order = f.order := by
  have h1 : ∀ (u : Kˣ) (g : LaurentSeries K), g ≠ 0 → g.order ≤ (qTwist u g).order := by
    intro u g hg
    have hne : qTwist u g ≠ 0 := (map_ne_zero_iff _ (qTwist_injective u)).mpr hg
    refine HahnSeries.order_le_of_coeff_ne_zero ?_
    intro h0
    apply hne
    apply HahnSeries.coeff_order_eq_zero.mp
    rw [qTwist_coeff, h0, mul_zero]
  refine le_antisymm ?_ (h1 v f hf)
  have h2 := h1 v⁻¹ (qTwist v f) ((map_ne_zero_iff _ (qTwist_injective v)).mpr hf)
  rwa [qTwist_qTwist, inv_mul_cancel, qTwist_one_apply] at h2

theorem coeff_algebraMap_mul (c : K) (y : LaurentSeries K) (i : ℤ) :
    (algebraMap K (LaurentSeries K) c * y).coeff i = c * y.coeff i := by
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.single_zero_mul_eq_smul, HahnSeries.coeff_smul,
    smul_eq_mul]

theorem coeff_slot_pow (v : Kˣ) (A : ℕ) [NeZero A] (n : ℕ) :
    ((qExpand K A (qTwist v (jqModC K))) ^ n).coeff (-((A * n : ℕ) : ℤ)) =
        ((v ^ (-(n : ℤ)) : Kˣ) : K) ∧
      ∀ i < -((A * n : ℕ) : ℤ), ((qExpand K A (qTwist v (jqModC K))) ^ n).coeff i = 0 := by
  rw [← map_pow, ← map_pow]
  constructor
  · rw [show -((A * n : ℕ) : ℤ) = (A : ℤ) * (-(n : ℤ)) by push_cast; ring, qExpand_coeff_mul,
      qTwist_coeff, coeff_jqModC_pow_self, mul_one]
  · intro i hi
    by_cases hdvd : (A : ℤ) ∣ i
    · obtain ⟨m, rfl⟩ := hdvd
      have hA : (0 : ℤ) < A := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne A)
      have hm : m < -(n : ℤ) := by
        refine lt_of_mul_lt_mul_left ?_ hA.le
        rw [mul_neg]; exact_mod_cast hi
      rw [qExpand_coeff_mul, qTwist_coeff, coeff_jqModC_pow_of_lt K hm, mul_zero]
    · exact qExpand_coeff_of_not_dvd A _ hdvd

theorem coeff_qExpand_jq_pow (A : ℕ) [NeZero A] (n : ℕ) :
    ((qExpand K A (jqModC K)) ^ n).coeff (-((A * n : ℕ) : ℤ)) = 1 ∧
      ∀ i < -((A * n : ℕ) : ℤ), ((qExpand K A (jqModC K)) ^ n).coeff i = 0 := by
  simpa [qTwist_one_apply] using coeff_slot_pow K 1 A n

theorem order_slot (v : Kˣ) (A : ℕ) [NeZero A] :
    (qExpand K A (qTwist v (jqModC K))).order = -(A : ℤ) := by
  obtain ⟨h1, h2⟩ := coeff_slot_pow K v A 1
  rw [pow_one, mul_one] at h1 h2
  exact order_eq_of_coeff K (by rw [h1]; exact Units.ne_zero _) h2

theorem order_qExpand_jq (A : ℕ) [NeZero A] : (qExpand K A (jqModC K)).order = -(A : ℤ) := by
  simpa [qTwist_one_apply] using order_slot K 1 A

theorem qExpand_mem_range_of_dvd (M P : ℕ) [NeZero M] [NeZero P] (h : M ∣ P) (f : LaurentSeries K) :
    qExpand K P f ∈ (qExpandAlgHomC K M).fieldRange := by
  haveI : NeZero (P / M) :=
    ⟨Nat.div_ne_zero_iff.mpr ⟨NeZero.ne M, Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne P)) h⟩⟩
  refine ⟨qExpand K (P / M) f, ?_⟩
  show qExpand K M (qExpand K (P / M) f) = qExpand K P f
  rw [qExpand_qExpand]
  exact qExpand_congr (Nat.mul_div_cancel' h) f

theorem socket (p : ℕ) [Fact p.Prime] (hpK : (p : K) ≠ 0) : jqNModC K p ∉ K⟮jqModC K⟯ := by
  rcases CharP.exists' K with hK | ⟨ℓ, hℓ, hKℓ⟩
  · haveI := hK; exact jqNModC_prime_not_mem_adjoin_of_charZero p
  · haveI := hℓ; haveI := hKℓ
    refine StarBank.starBank (ℓ := ℓ) ?_
    rintro rfl
    exact hpK (CharP.cast_eq_zero K p)

theorem natCast_ne_zero_of_dvd {M d : ℕ} (hM : (M : K) ≠ 0) (h : d ∣ M) : (d : K) ≠ 0 := by
  obtain ⟨c, rfl⟩ := h
  intro hd
  apply hM
  rw [Nat.cast_mul, hd, zero_mul]

theorem not_ringChar_dvd {M : ℕ} (hM : (M : K) ≠ 0) : ¬ ringChar K ∣ M :=
  fun h => hM ((ringChar.spec K M).mpr h)

theorem finrank_level (d : ℕ) [NeZero d] (hd : (d : K) ≠ 0) :
    Module.finrank K⟮jqModC K⟯ K⟮jqModC K⟯⟮jqNModC K d⟯ = dedekindPsi d :=
  finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket d fun p _ hp =>
    socket K p (natCast_ne_zero_of_dvd K hd hp)

theorem gen_level (d : ℕ) [NeZero d] (hd : (d : K) ≠ 0) :
    modularFunctionFieldC K d = adjoin K {x | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ d ∧ x = jqNModC K d'} :=
  (modularFunctionFieldC_eq_modularFunctionFieldFullC K (ringChar K) d (not_ringChar_dvd K hd)).trans rfl

theorem hall {M : ℕ} (hM : (M : K) ≠ 0) :
    ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank K⟮jqModC K⟯ K⟮jqModC K⟯⟮jqNModC K d⟯ = dedekindPsi d ∧
        modularFunctionFieldC K d = adjoin K {x | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ d ∧ x = jqNModC K d'} :=
  fun d hd _ => ⟨finrank_level K d (natCast_ne_zero_of_dvd K hM hd),
    gen_level K d (natCast_ne_zero_of_dvd K hM hd)⟩

end Laurent

section WithChar

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

def jF : modularFunctionFieldFullC K N := ⟨jqModC K, jqModC_mem_full K N⟩

def jNF : modularFunctionFieldFullC K N := ⟨jqNModC K N, jqModCd_mem_full K N dvd_rfl⟩

omit [NeZero N] in
@[scoped simp] theorem coe_jF : ((jF K N : modularFunctionFieldFullC K N) : LaurentSeries K) = jqModC K := rfl

@[scoped simp] theorem coe_jNF :
    ((jNF K N : modularFunctionFieldFullC K N) : LaurentSeries K) = jqNModC K N := rfl

omit [NeZero N] in
theorem jF_ne_zero : jF K N ≠ 0 := by
  intro h
  have := congrArg (fun x : modularFunctionFieldFullC K N => (x : LaurentSeries K)) h
  exact jqModC_ne_zero K this

variable [NeZero (N : K)]

theorem full_eq_adjoin_pair :
    modularFunctionFieldFullC K N = adjoin K {jqModC K, jqNModC K N} :=
  (modularFunctionFieldC_eq_modularFunctionFieldFullC K (ringChar K) N
    (not_ringChar_dvd K (NeZero.ne (N : K)))).symm

theorem full_eq_adjoin_adjoin :
    modularFunctionFieldFullC K N = (K⟮jqModC K⟯⟮jqNModC K N⟯).restrictScalars K := by
  rw [full_eq_adjoin_pair]
  exact (adjoin_simple_adjoin_simple K (jqModC K) (jqNModC K N)).symm

theorem finrank_adjoin_jqNModC :
    Module.finrank K⟮jqModC K⟯ K⟮jqModC K⟯⟮jqNModC K N⟯ = dedekindPsi N :=
  finrank_level K N (NeZero.ne (N : K))

theorem isIntegral_jqNModC : IsIntegral K⟮jqModC K⟯ (jqNModC K N) := by
  have hfin : FiniteDimensional K⟮jqModC K⟯ K⟮jqModC K⟯⟮jqNModC K N⟯ :=
    Module.finite_of_finrank_pos
      (by rw [finrank_adjoin_jqNModC]; exact dedekindPsi_pos N (NeZero.ne N))
  have h := IsIntegral.of_finite K⟮jqModC K⟯ (AdjoinSimple.gen K⟮jqModC K⟯ (jqNModC K N))
  rwa [isIntegral_iff, AdjoinSimple.coe_gen] at h

theorem natDegree_minpoly_jqNModC :
    (minpoly K⟮jqModC K⟯ (jqNModC K N)).natDegree = dedekindPsi N := by
  rw [← adjoin.finrank (isIntegral_jqNModC K N), finrank_adjoin_jqNModC]

theorem eval₂_minpoly_slot (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    (a b : ℕ) (ha : a ∣ N) (hb : b < N / a) (hg : Nat.gcd (Nat.gcd a b) (N / a) = 1) [NeZero a] :
    (minpoly K⟮jqModC K⟯ (jqNModC K N)).eval₂
        ((qExpand K N).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))
        (qExpand K (a * a) (qTwist (ζ ^ (b * a)) (jqModC K))) = 0 := by
  rw [← eval_map, minpoly_jqNModC_map_eq_prod_slots N ζ hζ (hall K (NeZero.ne (N : K))), eval_prod]
  refine Finset.prod_eq_zero (Nat.mem_divisors.mpr ⟨ha, NeZero.ne N⟩) ?_
  rw [eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb, hg⟩) ?_
  simp only [eval_sub, eval_X, eval_C, dif_neg (NeZero.ne a), sub_self]

theorem slotEmbedding (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    (a b : ℕ) (ha : a ∣ N) (hb : b < N / a) (hg : Nat.gcd (Nat.gcd a b) (N / a) = 1) [NeZero a] :
    ∃ ι : modularFunctionFieldFullC K N →ₐ[K] LaurentSeries K,
      ι (jF K N) = qExpand K N (jqModC K) ∧
      ι (jNF K N) = qExpand K (a * a) (qTwist (ζ ^ (b * a)) (jqModC K)) := by
  have hint := isIntegral_jqNModC K N
  let L := AdjoinRoot.lift ((qExpand K N).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))
    (qExpand K (a * a) (qTwist (ζ ^ (b * a)) (jqModC K)))
    (eval₂_minpoly_slot K N ζ hζ a b ha hb hg)
  let e := adjoinRootEquivAdjoin K⟮jqModC K⟯ hint
  let φ : K⟮jqModC K⟯⟮jqNModC K N⟯ →+* LaurentSeries K :=
    L.comp (e.symm : K⟮jqModC K⟯⟮jqNModC K N⟯ →+* AdjoinRoot (minpoly K⟮jqModC K⟯ (jqNModC K N)))
  have hφalg : ∀ x : K⟮jqModC K⟯,
      φ (algebraMap K⟮jqModC K⟯ K⟮jqModC K⟯⟮jqNModC K N⟯ x) = qExpand K N x := fun x => by
    show L (e.symm (algebraMap _ _ x)) = _
    rw [AlgEquiv.commutes, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]
    rfl
  have hφgen : φ (AdjoinSimple.gen K⟮jqModC K⟯ (jqNModC K N)) =
      qExpand K (a * a) (qTwist (ζ ^ (b * a)) (jqModC K)) := by
    show L (e.symm (AdjoinSimple.gen _ _)) = _
    rw [adjoinRootEquivAdjoin_symm_apply_gen, AdjoinRoot.lift_root]
  have hF := full_eq_adjoin_adjoin K N
  let ι' : (K⟮jqModC K⟯⟮jqNModC K N⟯).restrictScalars K →ₐ[K] LaurentSeries K :=
    { toRingHom := φ
      commutes' := fun c => by
        show φ (algebraMap K⟮jqModC K⟯ K⟮jqModC K⟯⟮jqNModC K N⟯ (algebraMap K K⟮jqModC K⟯ c)) = _
        rw [hφalg]
        show qExpand K N (algebraMap K (LaurentSeries K) c) = algebraMap K (LaurentSeries K) c
        rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }
  refine ⟨ι'.comp (inclusion hF.le), ?_, ?_⟩
  · exact hφalg ⟨jqModC K, mem_adjoin_simple_self K _⟩
  · exact hφgen

theorem slot_range (ζ : Kˣ) (a b : ℕ) (ha : a ∣ N) [NeZero a]
    [NeZero (a * Nat.gcd a (N / a))]
    (ι : modularFunctionFieldFullC K N →ₐ[K] LaurentSeries K)
    (hι₁ : ι (jF K N) = qExpand K N (jqModC K))
    (hι₂ : ι (jNF K N) = qExpand K (a * a) (qTwist (ζ ^ (b * a)) (jqModC K)))
    (x : modularFunctionFieldFullC K N) :
    ι x ∈ (qExpandAlgHomC K (a * Nat.gcd a (N / a))).fieldRange := by
  have ha0 : a ≠ 0 := NeZero.ne a
  have hag_dvd_N : a * Nat.gcd a (N / a) ∣ N := by
    calc a * Nat.gcd a (N / a) ∣ a * (N / a) := Nat.mul_dvd_mul_left a (Nat.gcd_dvd_right _ _)
      _ = N := Nat.mul_div_cancel' ha
  have hag_dvd_aa : a * Nat.gcd a (N / a) ∣ a * a := Nat.mul_dvd_mul_left a (Nat.gcd_dvd_left _ _)
  haveI : NeZero (a * a) := ⟨Nat.mul_ne_zero ha0 ha0⟩
  have htop : adjoin K ({jF K N, jNF K N} : Set (modularFunctionFieldFullC K N)) = ⊤ := by
    apply IntermediateField.map_injective (modularFunctionFieldFullC K N).val
    calc (adjoin K ({jF K N, jNF K N} : Set (modularFunctionFieldFullC K N))).map
          (modularFunctionFieldFullC K N).val
        = adjoin K ((modularFunctionFieldFullC K N).val '' {jF K N, jNF K N}) :=
          adjoin_map K _ (modularFunctionFieldFullC K N).val
      _ = adjoin K ({jqModC K, jqNModC K N} : Set (LaurentSeries K)) := by
          congr 1
          rw [Set.image_insert_eq, Set.image_singleton]
          rfl
      _ = modularFunctionFieldFullC K N := (full_eq_adjoin_pair K N).symm
      _ = (⊤ : IntermediateField K (modularFunctionFieldFullC K N)).map
            (modularFunctionFieldFullC K N).val :=
          (fieldRange_val (S := modularFunctionFieldFullC K N)).symm.trans
            (AlgHom.fieldRange_eq_map (modularFunctionFieldFullC K N).val)
  have hxmem : x ∈ adjoin K ({jF K N, jNF K N} : Set (modularFunctionFieldFullC K N)) :=
    htop ▸ mem_top
  induction hxmem using adjoin_induction with
  | mem y hy =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hι₁ ▸ qExpand_mem_range_of_dvd K _ N hag_dvd_N (jqModC K)
    · exact hι₂ ▸ qExpand_mem_range_of_dvd K _ (a * a) hag_dvd_aa (qTwist (ζ ^ (b * a)) (jqModC K))
  | algebraMap c =>
    rw [AlgHom.commutes]
    exact IntermediateField.algebraMap_mem _ c
  | add y z _ _ ihy ihz => rw [map_add]; exact add_mem ihy ihz
  | inv y _ ih => rw [map_inv₀]; exact inv_mem ih
  | mul y z _ _ ihy ihz => rw [map_mul]; exact mul_mem ihy ihz

theorem slotWidth (ζ : Kˣ) (a b : ℕ) (ha : a ∣ N) [NeZero a]
    (ι : modularFunctionFieldFullC K N →ₐ[K] LaurentSeries K)
    (hι₁ : ι (jF K N) = qExpand K N (jqModC K))
    (hι₂ : ι (jNF K N) = qExpand K (a * a) (qTwist (ζ ^ (b * a)) (jqModC K)))
    (w : Place K (modularFunctionFieldFullC K N)) (γ : ℤ) (hγ : 0 < γ)
    (hw : ∀ x, w.ord x * γ = (ι x).order) :
    γ = a * Nat.gcd a (N / a) ∧
    w.ord (jF K N) = -((N / a / Nat.gcd a (N / a) : ℕ) : ℤ) ∧
    w.ord (jNF K N) = -((a / Nat.gcd a (N / a) : ℕ) : ℤ) := by
  set g := Nat.gcd a (N / a) with hgdef
  have ha0 : a ≠ 0 := NeZero.ne a
  have hg0 : g ≠ 0 := Nat.gcd_ne_zero_left ha0
  haveI hag0 : NeZero (a * g) := ⟨Nat.mul_ne_zero ha0 hg0⟩
  have hag_dvd_N : a * g ∣ N := by
    calc a * g ∣ a * (N / a) := Nat.mul_dvd_mul_left a (Nat.gcd_dvd_right _ _)
      _ = N := Nat.mul_div_cancel' ha
  haveI : NeZero (a * a) := ⟨Nat.mul_ne_zero ha0 ha0⟩
  have hord1 : (ι (jF K N)).order = -(N : ℤ) := by
    rw [hι₁, order_qExpand, order_jqModC, mul_neg_one]
  have hord2 : (ι (jNF K N)).order = -((a * a : ℕ) : ℤ) := by
    rw [hι₂, order_qExpand, order_qTwist K _ (jqModC_ne_zero K), order_jqModC, mul_neg_one]
  have hw1 : w.ord (jF K N) * γ = -(N : ℤ) := (hw _).trans hord1
  have hw2 : w.ord (jNF K N) * γ = -((a * a : ℕ) : ℤ) := (hw _).trans hord2
  have hγdvd : γ ∣ ((a * g : ℕ) : ℤ) := by
    have hN : γ ∣ (N : ℤ) := ⟨-(w.ord (jF K N)), by rw [mul_neg, mul_comm γ, hw1, neg_neg]⟩
    have haa : γ ∣ ((a * a : ℕ) : ℤ) :=
      ⟨-(w.ord (jNF K N)), by rw [mul_neg, mul_comm γ, hw2, neg_neg]⟩
    have key : Nat.gcd N (a * a) = a * g := by
      conv_lhs => rw [← Nat.mul_div_cancel' ha]
      rw [Nat.gcd_mul_left, Nat.gcd_comm]
    rw [← key, Nat.gcd_eq_gcd_ab]
    exact dvd_add (Dvd.dvd.mul_right hN _) (Dvd.dvd.mul_right haa _)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨f, hfπ⟩ := slot_range K N ζ a b ha ι hι₁ hι₂ (π : modularFunctionFieldFullC K N)
  have hγeq : γ = (ι (π : modularFunctionFieldFullC K N)).order := by
    have := hw (π : modularFunctionFieldFullC K N)
    rw [w.ord_coe_irreducible hπ, one_mul] at this
    exact this
  have hagdvdγ : ((a * g : ℕ) : ℤ) ∣ γ := by
    rw [hγeq, ← hfπ]
    show ((a * g : ℕ) : ℤ) ∣ (qExpandAlgHomC K (a * g) f).order
    rw [qExpandAlgHomC_apply, order_qExpand]
    exact Dvd.intro _ rfl
  have hagpos : 0 < ((a * g : ℕ) : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hag0.out
  have hγval : γ = ((a * g : ℕ) : ℤ) :=
    Int.dvd_antisymm (le_of_lt hγ) (le_of_lt hagpos) hγdvd hagdvdγ
  refine ⟨by rw [hγval]; push_cast; ring, ?_, ?_⟩
  · have hdiv : (N / a / g) * (a * g) = N := by
      rw [Nat.div_div_eq_div_mul, Nat.div_mul_cancel hag_dvd_N]
    have key : (-((N / a / g : ℕ) : ℤ)) * ((a * g : ℕ) : ℤ) = -(N : ℤ) := by
      rw [neg_mul, ← Nat.cast_mul, hdiv]
    exact mul_right_cancel₀ (ne_of_gt hagpos) ((hγval ▸ hw1).trans key.symm)
  · have hdiv : (a / g) * (a * g) = a * a := by
      rw [mul_comm a g, ← mul_assoc, Nat.div_mul_cancel (Nat.gcd_dvd_left a (N / a))]
    have key : (-((a / g : ℕ) : ℤ)) * ((a * g : ℕ) : ℤ) = -((a * a : ℕ) : ℤ) := by
      rw [neg_mul, ← Nat.cast_mul, hdiv]
    exact mul_right_cancel₀ (ne_of_gt hagpos) ((hγval ▸ hw2).trans key.symm)

theorem slotOrbit (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    (a b : ℕ) (ha : a ∣ N) [NeZero a] (a' b' : ℕ) (ha' : a' ∣ N) [NeZero a']
    (ι ι' : modularFunctionFieldFullC K N →ₐ[K] LaurentSeries K)
    (hι₁ : ι (jF K N) = qExpand K N (jqModC K))
    (hι₂ : ι (jNF K N) = qExpand K (a * a) (qTwist (ζ ^ (b * a)) (jqModC K)))
    (hι'₁ : ι' (jF K N) = qExpand K N (jqModC K))
    (hι'₂ : ι' (jNF K N) = qExpand K (a' * a') (qTwist (ζ ^ (b' * a')) (jqModC K)))
    (w w' : Place K (modularFunctionFieldFullC K N)) (γ γ' : ℤ) (hγ : 0 < γ) (hγ' : 0 < γ')
    (hw : ∀ x, w.ord x * γ = (ι x).order) (hw' : ∀ x, w'.ord x * γ' = (ι' x).order) :
    w = w' ↔ a = a' ∧ b ≡ b' [MOD Nat.gcd a (N / a)] := by
  have _ := ha'
  have hFeq := full_eq_adjoin_pair K N
  obtain ⟨d, rfl⟩ := ha
  have ha0 : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  have had : a * d / a = d := Nat.mul_div_cancel_left d ha0
  rw [had]
  have hζu : IsPrimitiveRoot ζ (a * d) := IsPrimitiveRoot.coe_units_iff.mp hζ
  constructor
  · intro hww
    subst hww
    have h1 := hw (jF K (a * d))
    have h1' := hw' (jF K (a * d))
    rw [hι₁, order_qExpand_jq] at h1
    rw [hι'₁, order_qExpand_jq] at h1'
    have hne : w.ord (jF K (a * d)) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h1
      exact NeZero.ne (a * d) (by exact_mod_cast (neg_eq_zero.mp h1.symm))
    obtain rfl : γ = γ' := mul_left_cancel₀ hne (h1.trans h1'.symm)
    have h2 := hw (jNF K (a * d))
    have h2' := hw' (jNF K (a * d))
    rw [hι₂, order_slot] at h2
    rw [hι'₂, order_slot] at h2'
    have haa : a * a = a' * a' := by exact_mod_cast neg_injective (h2.symm.trans h2')
    obtain rfl : a = a' := Nat.mul_self_inj.mp haa
    refine ⟨rfl, ?_⟩
    obtain ⟨m, hm⟩ := Nat.gcd_dvd_left a d
    obtain ⟨n, hn⟩ := Nat.gcd_dvd_right a d
    set g := Nat.gcd a d with hg
    have hd0 : 0 < d := Nat.pos_of_ne_zero fun h => NeZero.ne (a * d) (by rw [h, mul_zero])
    have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => hd0.ne' (by rw [hn, h, mul_zero])
    have key : a * a * n = a * d * m := by
      calc a * a * n = a * (g * m) * n := by rw [← hm]
        _ = a * (g * n) * m := by ring
        _ = a * d * m := by rw [← hn]
    set c : K := (((ζ ^ (b * a)) ^ (-(n : ℤ)) : Kˣ) : K) with hc
    set x₀ : modularFunctionFieldFullC K (a * d) :=
      jNF K (a * d) ^ n - algebraMap K _ c * jF K (a * d) ^ m with hx₀
    have hιx : ι x₀ = (qExpand K (a * a) (qTwist (ζ ^ (b * a)) (jqModC K))) ^ n -
        algebraMap K (LaurentSeries K) c * (qExpand K (a * d) (jqModC K)) ^ m := by
      rw [hx₀, map_sub, map_mul, map_pow, map_pow, AlgHom.commutes, hι₁, hι₂]
    have hι'x : ι' x₀ = (qExpand K (a * a) (qTwist (ζ ^ (b' * a)) (jqModC K))) ^ n -
        algebraMap K (LaurentSeries K) c * (qExpand K (a * d) (jqModC K)) ^ m := by
      rw [hx₀, map_sub, map_mul, map_pow, map_pow, AlgHom.commutes, hι'₁, hι'₂]
    obtain ⟨hS1, -⟩ := coeff_slot_pow K (ζ ^ (b * a)) (a * a) n
    obtain ⟨hS1', hS2'⟩ := coeff_slot_pow K (ζ ^ (b' * a)) (a * a) n
    obtain ⟨hE1, hE2⟩ := coeff_qExpand_jq_pow K (a * d) m
    rw [← key] at hE1 hE2
    have hcoeffι : (ι x₀).coeff (-((a * a * n : ℕ) : ℤ)) = 0 := by
      rw [hιx, HahnSeries.coeff_sub, hS1, coeff_algebraMap_mul, hE1, mul_one, sub_self]
    have hbelow' : ∀ i < -((a * a * n : ℕ) : ℤ), (ι' x₀).coeff i = 0 := fun i hi => by
      rw [hι'x, HahnSeries.coeff_sub, hS2' i hi, coeff_algebraMap_mul, hE2 i hi, mul_zero, sub_zero]
    have hcoeffι' : (ι' x₀).coeff (-((a * a * n : ℕ) : ℤ)) =
        (((ζ ^ (b' * a)) ^ (-(n : ℤ)) : Kˣ) : K) - c := by
      rw [hι'x, HahnSeries.coeff_sub, hS1', coeff_algebraMap_mul, hE1, mul_one]
    have hordx : (ι' x₀).order = (ι x₀).order := (hw' x₀).symm.trans (hw x₀)
    have hM0 : (0 : ℤ) < ((a * a * n : ℕ) : ℤ) := by
      exact_mod_cast Nat.mul_pos (Nat.mul_pos ha0 ha0) hn0
    have hvan : (ι' x₀).coeff (-((a * a * n : ℕ) : ℤ)) = 0 := by
      by_cases hz : ι' x₀ = 0
      · rw [hz, HahnSeries.coeff_zero]
      refine HahnSeries.coeff_eq_zero_of_lt_order (lt_of_le_of_ne ?_ ?_)
      · by_contra! hlt
        exact hz (HahnSeries.coeff_order_eq_zero.mp (hbelow' _ hlt))
      · intro heq
        rw [hordx] at heq
        by_cases hz0 : ι x₀ = 0
        · rw [hz0, HahnSeries.order_zero] at heq
          exact hM0.ne' (neg_eq_zero.mp heq)
        · refine hz0 (HahnSeries.coeff_order_eq_zero.mp ?_)
          rw [← heq]
          exact hcoeffι
    rw [hcoeffι', sub_eq_zero, hc] at hvan
    have hu : (ζ ^ (b' * a)) ^ (-(n : ℤ)) = (ζ ^ (b * a)) ^ (-(n : ℤ)) := Units.ext hvan
    rw [zpow_neg, zpow_neg, inv_inj, zpow_natCast, zpow_natCast, ← pow_mul, ← pow_mul,
      pow_eq_pow_iff_modEq, ← hζu.eq_orderOf, show a * d = g * (a * n) by rw [hn]; ring,
      mul_assoc, mul_assoc] at hu
    exact (Nat.ModEq.mul_right_cancel' (Nat.mul_pos ha0 hn0).ne' hu).symm
  · rintro ⟨rfl, hbb⟩
    obtain ⟨q, hq⟩ := Nat.modEq_iff_dvd.mp hbb
    have hbez := Nat.gcd_eq_gcd_ab a d
    obtain ⟨k, hk⟩ : ∃ k : ℤ, (ζ ^ k) ^ ((a * a : ℕ) : ℤ) * ζ ^ (b * a) = ζ ^ (b' * a) := by
      refine ⟨Nat.gcdA a d * q, ?_⟩
      rw [← zpow_natCast ζ (b * a), ← zpow_natCast ζ (b' * a), ← zpow_mul, ← zpow_add,
        ← mul_inv_eq_one, ← zpow_sub, hζu.zpow_eq_one_iff_dvd]
      refine ⟨-(Nat.gcdB a d * q), ?_⟩
      push_cast
      linear_combination (-(a : ℤ)) * hq + (-(a : ℤ) * q) * hbez
    let T : LaurentSeries K →ₐ[K] LaurentSeries K :=
      { toRingHom := qTwist (ζ ^ k)
        commutes' := fun c => by
          show qTwist (ζ ^ k) (algebraMap K (LaurentSeries K) c) = algebraMap K (LaurentSeries K) c
          rw [algebraMap_laurentSeries_eq_single, qTwist_single, zpow_zero, Units.val_one, one_mul] }
    have hT : ι' = T.comp ι := by
      refine algHom_ext_of_eq_adjoin K hFeq fun x hx => ?_
      rcases hx with rfl | rfl
      · show ι' (jF K (a * d)) = qTwist (ζ ^ k) (ι (jF K (a * d)))
        rw [hι'₁, hι₁, qTwist_qExpand, ← zpow_mul, zpow_mul', zpow_natCast, hζu.pow_eq_one, one_zpow,
          qTwist_one_apply]
      · show ι' (jNF K (a * d)) = qTwist (ζ ^ k) (ι (jNF K (a * d)))
        rw [hι'₂, hι₂, qTwist_qExpand, qTwist_qTwist, hk]
    have hordeq : ∀ x, (ι' x).order = (ι x).order := fun x => by
      rw [hT]
      rcases eq_or_ne (ι x) 0 with h0 | h0
      · show (qTwist (ζ ^ k) (ι x)).order = (ι x).order
        rw [h0, map_zero]
      · exact order_qTwist K (ζ ^ k) h0
    apply Place.ext
    ext f
    rcases eq_or_ne f 0 with rfl | hf
    · exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
    rw [Place.mem_iff_ord_nonneg w hf, Place.mem_iff_ord_nonneg w' hf]
    have e1 := mul_nonneg_iff_of_pos_right (b := w.ord f) hγ
    have e2 := mul_nonneg_iff_of_pos_right (b := w'.ord f) hγ'
    rw [hw] at e1
    rw [hw', hordeq] at e2
    exact e1.symm.trans e2

theorem card_slotFinset (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N) :
    (slotFinset N).card = dedekindPsi N := by
  have hint := isIntegral_jqNModC K N
  have h := congrArg Polynomial.natDegree
    (minpoly_jqNModC_map_eq_prod_slots N ζ hζ (hall K (NeZero.ne (N : K))))
  rw [(minpoly.monic hint).natDegree_map, natDegree_minpoly_jqNModC,
    natDegree_prod_of_monic _ _ fun a _ => monic_prod_of_monic _ _ fun b _ => monic_X_sub_C _] at h
  rw [slotFinset, Finset.card_sigma, h]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [natDegree_prod_of_monic _ _ fun b _ => monic_X_sub_C _]
  simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]

theorem separable_minpoly (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N) :
    (minpoly K⟮jqModC K⟯ (jqNModC K N)).Separable := by
  have hζu : IsPrimitiveRoot ζ N := IsPrimitiveRoot.coe_units_iff.mp hζ
  rw [← Polynomial.separable_map ((qExpand K N).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K))),
    minpoly_jqNModC_map_eq_prod_slots N ζ hζ (hall K (NeZero.ne (N : K)))]
  have hprod : ∏ s ∈ slotFinset N, (X - C (if h : s.1 = 0 then 0 else
      letI : NeZero s.1 := ⟨h⟩; qExpand K (s.1 * s.1) (qTwist (ζ ^ (s.2 * s.1)) (jqModC K)))) =
      ∏ a ∈ N.divisors, ∏ b ∈ (Finset.range (N / a)).filter
        (fun b => Nat.gcd (Nat.gcd a b) (N / a) = 1), (X - C (if h : a = 0 then 0 else
          letI : NeZero a := ⟨h⟩; qExpand K (a * a) (qTwist (ζ ^ (b * a)) (jqModC K)))) :=
    Finset.prod_sigma _ _ _
  rw [← hprod]
  refine Polynomial.separable_prod_X_sub_C_iff'.mpr ?_
  rintro ⟨a, b⟩ hs ⟨a', b'⟩ hs' heq
  have hs1 := (mem_slotFinset (N := N) ⟨a, b⟩).mp hs
  have hs1' := (mem_slotFinset (N := N) ⟨a', b'⟩).mp hs'
  simp only at hs1 hs1' heq
  have ha0 : a ≠ 0 := fun h => NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ hs1.1))
  have ha0' : a' ≠ 0 := fun h => NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ hs1'.1))
  rw [dif_neg ha0, dif_neg ha0'] at heq
  haveI : NeZero a := ⟨ha0⟩
  haveI : NeZero a' := ⟨ha0'⟩
  haveI : NeZero (a * a) := ⟨Nat.mul_ne_zero ha0 ha0⟩
  haveI : NeZero (a' * a') := ⟨Nat.mul_ne_zero ha0' ha0'⟩
  have hord := congrArg HahnSeries.order heq
  rw [order_slot, order_slot, neg_inj] at hord
  have haa : a * a = a' * a' := by exact_mod_cast hord
  obtain rfl : a = a' := Nat.mul_self_inj.mp haa
  obtain ⟨h1, -⟩ := coeff_slot_pow K (ζ ^ (b * a)) (a * a) 1
  obtain ⟨h1', -⟩ := coeff_slot_pow K (ζ ^ (b' * a)) (a * a) 1
  rw [pow_one] at h1 h1'
  rw [heq, h1'] at h1
  have hu : (ζ ^ (b' * a)) ^ (-((1 : ℕ) : ℤ)) = (ζ ^ (b * a)) ^ (-((1 : ℕ) : ℤ)) := Units.ext h1
  rw [zpow_neg, zpow_neg, inv_inj, Nat.cast_one, zpow_one, zpow_one, pow_eq_pow_iff_modEq,
    ← hζu.eq_orderOf] at hu
  obtain ⟨d, hd⟩ := hs1.1
  have ha0p : 0 < a := Nat.pos_of_ne_zero ha0
  have hNa : N / a = d := by rw [hd, Nat.mul_div_cancel_left d ha0p]
  rw [hd, show a * d = d * a by ring] at hu
  have hbb : b' ≡ b [MOD d] := Nat.ModEq.mul_right_cancel' ha0 hu
  have hb : b < d := hNa ▸ hs1.2.1
  have hb' : b' < d := hNa ▸ hs1'.2.1
  have := (Nat.ModEq.eq_of_lt_of_lt hbb hb' hb).symm
  subst this
  rfl

theorem isSeparable_adjoin (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N) :
    Algebra.IsSeparable K⟮jqModC K⟯ K⟮jqModC K⟯⟮jqNModC K N⟯ :=
  (isSeparable_adjoin_simple_iff_isSeparable _ _).2 (separable_minpoly K N ζ hζ)

def sigmaA : RatFunc K ≃ₐ[K] K⟮jqModC K⟯ :=
  RatFunc.algEquivOfTranscendental _ (transcendental_jqModC K)

omit [NeZero N] [NeZero (N : K)] in
theorem coe_sigmaA_X :
    ((sigmaA K (RatFunc.X : RatFunc K) : K⟮jqModC K⟯) : LaurentSeries K) = jqModC K :=
  RatFunc.algEquivOfTranscendental_X _ _

theorem mem_full_iff (x : LaurentSeries K) :
    x ∈ modularFunctionFieldFullC K N ↔ x ∈ K⟮jqModC K⟯⟮jqNModC K N⟯ := by
  rw [full_eq_adjoin_adjoin K N, mem_restrictScalars]

def jTr : K⟮jqModC K⟯⟮jqNModC K N⟯ ≃+* modularFunctionFieldFullC K N where
  toFun x := ⟨x, (mem_full_iff K N _).mpr x.2⟩
  invFun y := ⟨y, (mem_full_iff K N _).mp y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem coe_jTr (x : K⟮jqModC K⟯⟮jqNModC K N⟯) :
    ((jTr K N x : modularFunctionFieldFullC K N) : LaurentSeries K) = x := by
  unfold jTr; rfl

def phiRF : RatFunc K →+* modularFunctionFieldFullC K N :=
  (jTr K N).toRingHom.comp
    ((algebraMap (K⟮jqModC K⟯) (K⟮jqModC K⟯⟮jqNModC K N⟯)).comp (sigmaA K).toRingEquiv.toRingHom)

theorem phiRF_apply (x : RatFunc K) :
    phiRF K N x = jTr K N (algebraMap (K⟮jqModC K⟯) (K⟮jqModC K⟯⟮jqNModC K N⟯) (sigmaA K x)) :=
  rfl

omit [NeZero (N : K)] in
theorem coe_algebraMap_tower (y : K⟮jqModC K⟯) :
    ((algebraMap (K⟮jqModC K⟯) (K⟮jqModC K⟯⟮jqNModC K N⟯) y : K⟮jqModC K⟯⟮jqNModC K N⟯) :
      LaurentSeries K) = y := by
  rw [IntermediateField.coe_algebraMap_apply]
  rfl

theorem coe_phiRF (x : RatFunc K) :
    ((phiRF K N x : modularFunctionFieldFullC K N) : LaurentSeries K) = (sigmaA K x : LaurentSeries K) := by
  rw [phiRF_apply, coe_jTr, coe_algebraMap_tower]

theorem phiRF_algebraMap (k : K) :
    phiRF K N (algebraMap K (RatFunc K) k) = algebraMap K (modularFunctionFieldFullC K N) k := by
  apply Subtype.ext
  rw [coe_phiRF, AlgEquiv.commutes]
  rfl

theorem phiRF_X : phiRF K N (RatFunc.X : RatFunc K) = jF K N := by
  apply Subtype.ext
  rw [coe_phiRF, coe_jF, coe_sigmaA_X]

abbrev algRatFunc : Algebra (RatFunc K) (modularFunctionFieldFullC K N) := (phiRF K N).toAlgebra

attribute [local instance] algRatFunc

theorem algebraMap_ratFunc_eq :
    algebraMap (RatFunc K) (modularFunctionFieldFullC K N) = phiRF K N := rfl

theorem isScalarTower_ratFunc : IsScalarTower K (RatFunc K) (modularFunctionFieldFullC K N) :=
  IsScalarTower.of_algebraMap_eq fun k => (phiRF_algebraMap K N k).symm

attribute [local instance] isScalarTower_ratFunc

theorem he_compat :
    (algebraMap (RatFunc K) (modularFunctionFieldFullC K N)).comp
        ((sigmaA K).symm.toRingEquiv : K⟮jqModC K⟯ ≃+* RatFunc K).toRingHom
      = (jTr K N).toRingHom.comp (algebraMap (K⟮jqModC K⟯) (K⟮jqModC K⟯⟮jqNModC K N⟯)) := by
  apply RingHom.ext
  intro y
  show phiRF K N ((sigmaA K).symm y) = jTr K N (algebraMap _ _ y)
  rw [phiRF_apply, AlgEquiv.apply_symm_apply]

theorem finite_ratFunc : Module.Finite (RatFunc K) (modularFunctionFieldFullC K N) := by
  haveI : FiniteDimensional (K⟮jqModC K⟯) (K⟮jqModC K⟯⟮jqNModC K N⟯) :=
    Module.finite_of_finrank_pos
      (by rw [finrank_adjoin_jqNModC K N]; exact dedekindPsi_pos N (NeZero.ne N))
  exact Module.Finite.of_equiv_equiv
    ((sigmaA K).symm.toRingEquiv : K⟮jqModC K⟯ ≃+* RatFunc K) (jTr K N) (he_compat K N)

attribute [local instance] finite_ratFunc

theorem finrank_ratFunc :
    Module.finrank (RatFunc K) (modularFunctionFieldFullC K N) = dedekindPsi N := by
  rw [← Algebra.finrank_eq_of_equiv_equiv
    ((sigmaA K).symm.toRingEquiv : K⟮jqModC K⟯ ≃+* RatFunc K) (jTr K N) (he_compat K N)]
  exact finrank_adjoin_jqNModC K N

theorem isSeparable_ratFunc (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N) :
    Algebra.IsSeparable (RatFunc K) (modularFunctionFieldFullC K N) := by
  haveI := isSeparable_adjoin K N ζ hζ
  exact Algebra.IsSeparable.of_equiv_equiv
    ((sigmaA K).symm.toRingEquiv : K⟮jqModC K⟯ ≃+* RatFunc K) (jTr K N) (he_compat K N)

theorem restrict_eq_of_ord_neg_pair (u u' : Place K (modularFunctionFieldFullC K N))
    (hu : u.ord (jF K N) < 0) (hu' : u'.ord (jF K N) < 0) :
    u.restrict (RatFunc K) = u'.restrict (RatFunc K) := by
  have key : ∀ u₀ : Place K (modularFunctionFieldFullC K N), u₀.ord (jF K N) < 0 →
      ∀ p : IsDedekindDomain.HeightOneSpectrum (Polynomial K),
        u₀.restrict (RatFunc K) ≠ Place.ofHeightOneSpectrum p := by
    intro u₀ hu₀ p heq
    have hX : (RatFunc.X : RatFunc K) ∈ (u₀.restrict (RatFunc K)).toValuationSubring := by
      rw [heq, Place.ofHeightOneSpectrum_toValuationSubring, Valuation.mem_valuationSubring_iff,
        ← RatFunc.algebraMap_X]
      exact p.valuation_le_one _
    rw [Place.mem_restrict_iff, algebraMap_ratFunc_eq, phiRF_X,
      Place.mem_iff_ord_nonneg _ (jF_ne_zero K N)] at hX
    omega
  exact RationalFunctionField.subsingleton_setOf_forall_ne_ofHeightOneSpectrum
    (key u hu) (key u' hu')

omit [NeZero N] [NeZero (N : K)] in

theorem exists_refCusp :
    ∃ w₀ : Place K (modularFunctionFieldFullC K N), w₀.ord (jF K N) = -1 := by
  obtain ⟨w₀, γ, hγ, hw⟩ := Place.exists_ord_mul_eq_order_of_algHom_laurentSeries K
    (modularFunctionFieldFullC K N).val ⟨jF K N, by
      show ((jF K N : modularFunctionFieldFullC K N) : LaurentSeries K).order ≠ 0
      rw [coe_jF, order_jqModC]; decide⟩
  have h := hw (jF K N)
  have h' : ((jF K N : modularFunctionFieldFullC K N) : LaurentSeries K).order = -1 := by
    rw [coe_jF, order_jqModC]
  rw [show ((modularFunctionFieldFullC K N).val (jF K N)) = ((jF K N : modularFunctionFieldFullC K N)
    : LaurentSeries K) from rfl, h'] at h
  refine ⟨w₀, ?_⟩
  have hγ1 : (1 : ℤ) ≤ γ := by exact_mod_cast hγ
  rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one' h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · omega
  · exact h1

theorem ramificationIndex_eq_neg_ord (u : Place K (modularFunctionFieldFullC K N))
    (hu : u.ord (jF K N) < 0) :
    (u.ramificationIndex (RatFunc K) : ℤ) = -(u.ord (jF K N)) := by
  obtain ⟨w₀, h₀⟩ := exists_refCusp K N
  have hc₀ : w₀.ord (jF K N) < 0 := by omega
  have h1 := w₀.ord_restrict (F := RatFunc K) (RatFunc.X)
  rw [algebraMap_ratFunc_eq, phiRF_X, h₀] at h1
  have hepos₀ : (0 : ℤ) < (w₀.ramificationIndex (RatFunc K) : ℤ) := by
    exact_mod_cast w₀.ramificationIndex_pos (F := RatFunc K)
  have he₀ : ((w₀.ramificationIndex (RatFunc K) : ℤ)) = 1 := by
    refine Int.eq_one_of_mul_eq_one_right hepos₀.le (b := -(w₀.restrict (RatFunc K)).ord RatFunc.X) ?_
    linarith [h1]
  have hX : (w₀.restrict (RatFunc K)).ord RatFunc.X = -1 := by
    rw [he₀, one_mul] at h1
    linarith
  have h2 := u.ord_restrict (F := RatFunc K) (RatFunc.X)
  rw [algebraMap_ratFunc_eq, phiRF_X, restrict_eq_of_ord_neg_pair K N u w₀ hu hc₀, hX] at h2
  omega

theorem exists_slotData (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N) :
    ∀ s : (Σ _ : ℕ, ℕ), s ∈ slotFinset N →
      ∃ (_ : NeZero s.1) (ι : modularFunctionFieldFullC K N →ₐ[K] LaurentSeries K)
        (u : Place K (modularFunctionFieldFullC K N)),
        ι (jF K N) = qExpand K N (jqModC K) ∧
        ι (jNF K N) = qExpand K (s.1 * s.1) (qTwist (ζ ^ (s.2 * s.1)) (jqModC K)) ∧
        (∀ x, u.ord x * ((s.1 * Nat.gcd s.1 (N / s.1) : ℕ) : ℤ) = (ι x).order) ∧
        u.ord (jF K N) = -((N / s.1 / Nat.gcd s.1 (N / s.1) : ℕ) : ℤ) := by
  rintro ⟨a, b⟩ hs
  rw [mem_slotFinset] at hs
  obtain ⟨haN, hblt, hgcd⟩ := hs
  have ha0 : a ≠ 0 := fun h => NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ haN))
  haveI : NeZero a := ⟨ha0⟩
  obtain ⟨ι, hι₁, hι₂⟩ := slotEmbedding K N ζ hζ a b haN hblt hgcd
  have hordj : (ι (jF K N)).order = (N : ℤ) * (-1) := by
    rw [hι₁, order_qExpand, order_jqModC]
  obtain ⟨u, γn, hγn, hwn⟩ := Place.exists_ord_mul_eq_order_of_algHom_laurentSeries K ι
    ⟨jF K N, by rw [hordj]; simp [NeZero.ne N]⟩
  obtain ⟨hγeq, hoj, -⟩ := slotWidth K N ζ a b haN ι hι₁ hι₂ u (γn : ℤ)
    (by exact_mod_cast hγn) hwn
  refine ⟨‹NeZero a›, ι, u, hι₁, hι₂, ?_, ?_⟩
  · intro x
    have := hwn x
    rwa [hγeq, ← Nat.cast_mul] at this
  · exact hoj

theorem main_exhaustion (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    (w : Place K (modularFunctionFieldFullC K N)) (hc : w.ord (jF K N) < 0) :
    ∃ a b : ℕ, a ∣ N ∧ b < N / a ∧ Nat.gcd (Nat.gcd a b) (N / a) = 1 ∧
      ∃ (_ : NeZero a) (ι : modularFunctionFieldFullC K N →ₐ[K] LaurentSeries K),
        ι (jF K N) = qExpand K N (jqModC K) ∧
        ι (jNF K N) = qExpand K (a * a) (qTwist (ζ ^ (b * a)) (jqModC K)) ∧
        ∀ x, w.ord x * ((a * Nat.gcd a (N / a) : ℕ) : ℤ) = (ι x).order := by
  classical
  haveI := isSeparable_ratFunc K N ζ hζ
  choose nz ι place hι₁ hι₂ hword hordj using exists_slotData K N ζ hζ
  set f : (Σ _ : ℕ, ℕ) → Place K (modularFunctionFieldFullC K N) :=
    fun s => if hs : s ∈ slotFinset N then place s hs else w with hf
  have hf_mem : ∀ s (hs : s ∈ slotFinset N), f s = place s hs := fun s hs => by
    simp [hf, hs]
  have hapos : ∀ s, s ∈ slotFinset N → 0 < s.1 := fun s hs =>
    Nat.pos_of_ne_zero fun h => NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ ((mem_slotFinset s).mp hs).1))
  have hcusp : ∀ s (hs : s ∈ slotFinset N), (place s hs).ord (jF K N) < 0 := by
    intro s hs
    have h1 : 0 < N / s.1 := Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) ((mem_slotFinset s).mp hs).1) (hapos s hs)
    have h2 : 0 < N / s.1 / Nat.gcd s.1 (N / s.1) := Nat.div_pos
      (Nat.le_of_dvd h1 (Nat.gcd_dvd_right s.1 (N / s.1)))
      (Nat.gcd_pos_of_pos_right s.1 h1)
    rw [hordj s hs]
    omega
  have hexists : ∃ s : (Σ _ : ℕ, ℕ), ∃ hs : s ∈ slotFinset N, w = place s hs := by
    by_contra hno
    push Not at hno
    set PS : Finset (Place K (modularFunctionFieldFullC K N)) := (slotFinset N).image f with hPS
    have hwPS : w ∉ PS := by
      rw [hPS]
      simp only [Finset.mem_image, not_exists, not_and]
      intro s hs heq
      exact hno s hs (by rw [← hf_mem s hs, heq])
    have hS : ∀ u ∈ insert w PS, u.restrict (RatFunc K) = w.restrict (RatFunc K) := by
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · rfl
      · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hu
        rw [hf_mem s hs]
        exact restrict_eq_of_ord_neg_pair K N _ w (hcusp s hs) hc
    have hsum := Place.sum_ramificationIndex_mul_inertiaDeg_le_finrank
      (w.restrict (RatFunc K)) (insert w PS) hS
    rw [finrank_ratFunc] at hsum
    have hfib : ∀ u ∈ PS, ∃ (s₀ : (Σ _ : ℕ, ℕ)) (hs₀ : s₀ ∈ slotFinset N), u = place s₀ hs₀ := by
      intro u hu
      obtain ⟨s₀, hs₀, rfl⟩ := Finset.mem_image.mp hu
      exact ⟨s₀, hs₀, (hf_mem s₀ hs₀)⟩
    have hP : ∀ s ∈ slotFinset N, ∀ s' ∈ slotFinset N,
        (f s = f s' ↔ s.1 = s'.1 ∧ s.2 ≡ s'.2 [MOD Nat.gcd s.1 (N / s.1)]) := by
      intro s hs s' hs'
      have h1 := (mem_slotFinset s).mp hs
      have h2 := (mem_slotFinset s').mp hs'
      haveI : NeZero s.1 := ⟨(hapos s hs).ne'⟩
      haveI : NeZero s'.1 := ⟨(hapos s' hs').ne'⟩
      have hpos1 : (0 : ℤ) < ((s.1 * Nat.gcd s.1 (N / s.1) : ℕ) : ℤ) := by
        exact_mod_cast Nat.mul_pos (hapos s hs) (Nat.gcd_pos_of_pos_left _ (hapos s hs))
      have hpos2 : (0 : ℤ) < ((s'.1 * Nat.gcd s'.1 (N / s'.1) : ℕ) : ℤ) := by
        exact_mod_cast Nat.mul_pos (hapos s' hs') (Nat.gcd_pos_of_pos_left _ (hapos s' hs'))
      rw [hf_mem s hs, hf_mem s' hs']
      exact slotOrbit K N ζ hζ s.1 s.2 h1.1 s'.1 s'.2 h2.1 (ι s hs) (ι s' hs') (hι₁ s hs) (hι₂ s hs)
        (hι₁ s' hs') (hι₂ s' hs') (place s hs) (place s' hs')
        ((s.1 * Nat.gcd s.1 (N / s.1) : ℕ) : ℤ) ((s'.1 * Nat.gcd s'.1 (N / s'.1) : ℕ) : ℤ)
        hpos1 hpos2 (hword s hs) (hword s' hs')
    have hcount0 : (slotFinset N).card = ∑ u ∈ PS, ((slotFinset N).filter (fun s => f s = u)).card :=
      Finset.card_eq_sum_card_fiberwise (fun s hs => Finset.mem_image_of_mem f hs)
    have hperu : ∀ u ∈ PS, (((slotFinset N).filter (fun s => f s = u)).card : ℤ)
        ≤ (u.ramificationIndex (RatFunc K) : ℤ) * (u.inertiaDeg (RatFunc K) : ℤ) := by
      intro u hu
      obtain ⟨s₀, hs₀, rfl⟩ := hfib u hu
      have hcard : ((slotFinset N).filter (fun s => f s = place s₀ hs₀)).card =
          N / s₀.1 / Nat.gcd s₀.1 (N / s₀.1) := by
        rw [← hf_mem s₀ hs₀]
        exact card_slotFibre N f hP s₀ hs₀
      have he := ramificationIndex_eq_neg_ord K N (place s₀ hs₀) (hcusp s₀ hs₀)
      rw [hordj s₀ hs₀, neg_neg] at he
      have hf1 : (1 : ℤ) ≤ ((place s₀ hs₀).inertiaDeg (RatFunc K) : ℤ) := by
        exact_mod_cast Place.inertiaDeg_pos (F := RatFunc K) (place s₀ hs₀)
      have hepos : (0 : ℤ) ≤ ((place s₀ hs₀).ramificationIndex (RatFunc K) : ℤ) := by positivity
      calc (((slotFinset N).filter (fun s => f s = place s₀ hs₀)).card : ℤ)
          = ((N / s₀.1 / Nat.gcd s₀.1 (N / s₀.1) : ℕ) : ℤ) := by exact_mod_cast hcard
        _ = ((place s₀ hs₀).ramificationIndex (RatFunc K) : ℤ) := he.symm
        _ ≤ _ := le_mul_of_one_le_right hepos hf1
    have hge : (dedekindPsi N : ℤ) ≤
        ∑ u ∈ PS, (u.ramificationIndex (RatFunc K) : ℤ) * (u.inertiaDeg (RatFunc K) : ℤ) := by
      calc (dedekindPsi N : ℤ) = ((slotFinset N).card : ℤ) := by rw [card_slotFinset K N ζ hζ]
        _ = ∑ u ∈ PS, (((slotFinset N).filter (fun s => f s = u)).card : ℤ) := by
            rw [hcount0]; push_cast; rfl
        _ ≤ _ := Finset.sum_le_sum hperu
    have hw1 : (1 : ℤ) ≤ (w.ramificationIndex (RatFunc K) : ℤ) * (w.inertiaDeg (RatFunc K) : ℤ) := by
      have e1 : (1 : ℤ) ≤ (w.ramificationIndex (RatFunc K) : ℤ) := by
        exact_mod_cast w.ramificationIndex_pos (F := RatFunc K)
      have f1 : (1 : ℤ) ≤ (w.inertiaDeg (RatFunc K) : ℤ) := by
        exact_mod_cast Place.inertiaDeg_pos (F := RatFunc K) w
      have := mul_le_mul e1 f1 zero_le_one (le_trans zero_le_one e1)
      simpa using this
    rw [Finset.sum_insert hwPS] at hsum
    linarith
  obtain ⟨⟨a, b⟩, hs, rfl⟩ := hexists
  have hmem := (mem_slotFinset _).mp hs
  haveI : NeZero a := ⟨(hapos _ hs).ne'⟩
  exact ⟨a, b, hmem.1, hmem.2.1, hmem.2.2,
    ⟨‹NeZero a›, ι ⟨a, b⟩ hs, hι₁ ⟨a, b⟩ hs, hι₂ ⟨a, b⟩ hs, hword ⟨a, b⟩ hs⟩⟩

def SlotAt (ζ : Kˣ) (a b : ℕ) (w : Place K (modularFunctionFieldFullC K N)) : Prop :=
  ∃ (_ : NeZero a) (ι : modularFunctionFieldFullC K N →ₐ[K] LaurentSeries K) (γ : ℤ),
    0 < γ ∧
    ι (jF K N) = qExpand K N (jqModC K) ∧
    ι (jNF K N) = qExpand K (a * a) (qTwist (ζ ^ (b * a)) (jqModC K)) ∧
    ∀ x, w.ord x * γ = (ι x).order

omit [NeZero (N : K)] in
theorem div_pos_of_dvd {a : ℕ} (ha : a ∣ N) : 0 < N / a :=
  Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) ha)
    (Nat.pos_of_ne_zero fun h => NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ ha)))

omit [NeZero (N : K)] in
theorem gcd_pos_of_dvd {a : ℕ} (ha : a ∣ N) : 0 < Nat.gcd a (N / a) :=
  Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero fun h => NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ ha)))

theorem exists_slotAt (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N) {a b : ℕ} (ha : a ∣ N)
    (hb : b < Nat.gcd a (N / a)) (hcop : Nat.Coprime (Nat.gcd a (N / a)) b) :
    ∃ w, SlotAt K N ζ a b w := by
  haveI : NeZero a := ⟨fun h => NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ ha))⟩
  have hb' : b < N / a :=
    lt_of_lt_of_le hb (Nat.le_of_dvd (div_pos_of_dvd N ha) (Nat.gcd_dvd_right _ _))
  have hg : Nat.gcd (Nat.gcd a b) (N / a) = 1 := by
    rw [gcd_gcd_swap]
    exact Nat.coprime_iff_gcd_eq_one.mp hcop
  obtain ⟨ι, h1, h2⟩ := slotEmbedding K N ζ hζ a b ha hb' hg
  have hne : ∃ x, (ι x).order ≠ 0 :=
    ⟨jF K N, by rw [h1, order_qExpand_jq]; simp [NeZero.ne N]⟩
  obtain ⟨w, γ, hγ, hw⟩ := Place.exists_ord_mul_eq_order_of_algHom_laurentSeries K ι hne
  exact ⟨w, ‹NeZero a›, ι, γ, by exact_mod_cast hγ, h1, h2, hw⟩

theorem ord_neg_of_slotAt (ζ : Kˣ) {a b : ℕ} (ha : a ∣ N)
    {w : Place K (modularFunctionFieldFullC K N)} (h : SlotAt K N ζ a b w) :
    w.ord (jF K N) < 0 := by
  obtain ⟨_, ι, γ, hγ, h1, h2, hw⟩ := h
  obtain ⟨-, hj, -⟩ := slotWidth K N ζ a b ha ι h1 h2 w γ hγ hw
  rw [hj]
  have hpos : 0 < N / a / Nat.gcd a (N / a) :=
    Nat.div_pos (Nat.le_of_dvd (div_pos_of_dvd N ha) (Nat.gcd_dvd_right _ _)) (gcd_pos_of_dvd N ha)
  omega

theorem slotAt_eq_iff (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N) {a b a' b' : ℕ}
    (ha : a ∣ N) (ha' : a' ∣ N) {w w' : Place K (modularFunctionFieldFullC K N)}
    (h : SlotAt K N ζ a b w) (h' : SlotAt K N ζ a' b' w') :
    w = w' ↔ a = a' ∧ b ≡ b' [MOD Nat.gcd a (N / a)] := by
  obtain ⟨_, ι, γ, hγ, h1, h2, hw⟩ := h
  obtain ⟨_, ι', γ', hγ', h1', h2', hw'⟩ := h'
  exact slotOrbit K N ζ hζ a b ha a' b' ha' ι ι' h1 h2 h1' h2' w w' γ γ' hγ hγ' hw hw'

theorem exists_slotAt_of_ord_neg (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    {v : Place K (modularFunctionFieldFullC K N)} (hv : v.ord (jF K N) < 0) :
    ∃ a b : ℕ, a ∣ N ∧ Nat.Coprime (Nat.gcd a (N / a)) b ∧ SlotAt K N ζ a b v := by
  obtain ⟨a, b, ha, -, hg, hne, ι, h1, h2, hw⟩ := main_exhaustion K N ζ hζ v hv
  refine ⟨a, b, ha, ?_, hne, ι, ((a * Nat.gcd a (N / a) : ℕ) : ℤ), ?_, h1, h2, hw⟩
  · rw [gcd_gcd_swap] at hg
    exact Nat.coprime_iff_gcd_eq_one.mpr hg
  · haveI := hne
    exact_mod_cast Nat.mul_pos (NeZero.pos a) (gcd_pos_of_dvd N ha)

theorem card_poles_eq_cuspCount (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    (T : Finset (Place K (modularFunctionFieldFullC K N)))
    (hT : ∀ P, P ∈ T ↔ P.ord (jF K N) < 0) : T.card = cuspCount N := by
  classical
  have hex : ∀ p ∈ labels N, ∃ w, SlotAt K N ζ p.1 p.2 w := fun p hp => by
    obtain ⟨h1, h2, h3⟩ := (mem_labels p).mp hp
    exact exists_slotAt K N ζ hζ h1 h2 h3
  rw [← card_labels N]
  symm
  refine Finset.card_bij (fun p hp => (hex p hp).choose) ?_ ?_ ?_
  · intro p hp
    exact (hT _).mpr (ord_neg_of_slotAt K N ζ ((mem_labels p).mp hp).1 (hex p hp).choose_spec)
  · intro p hp p' hp' heq
    obtain ⟨ha, hb, -⟩ := (mem_labels p).mp hp
    obtain ⟨ha', hb', -⟩ := (mem_labels p').mp hp'
    obtain ⟨hpa, hmod⟩ :=
      (slotAt_eq_iff K N ζ hζ ha ha' (hex p hp).choose_spec (hex p' hp').choose_spec).mp heq
    obtain ⟨a, b⟩ := p
    obtain ⟨a', b'⟩ := p'
    dsimp only at hpa hmod ha hb ha' hb'
    subst hpa
    obtain rfl : b = b' := Nat.ModEq.eq_of_lt_of_lt hmod hb hb'
    rfl
  · intro v hv
    obtain ⟨a, b, ha, hcop, hslot⟩ := exists_slotAt_of_ord_neg K N ζ hζ ((hT v).mp hv)
    have hg : 0 < Nat.gcd a (N / a) := gcd_pos_of_dvd N ha
    have hmem : (⟨a, b % Nat.gcd a (N / a)⟩ : Σ _ : ℕ, ℕ) ∈ labels N := by
      refine (mem_labels _).mpr ⟨ha, Nat.mod_lt _ hg, ?_⟩
      show Nat.Coprime (Nat.gcd a (N / a)) (b % Nat.gcd a (N / a))
      rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm (Nat.gcd a (N / a)) (b % Nat.gcd a (N / a)),
        ← Nat.gcd_rec]
      exact Nat.coprime_iff_gcd_eq_one.mp hcop
    refine ⟨⟨a, b % Nat.gcd a (N / a)⟩, hmem, ?_⟩
    exact (slotAt_eq_iff K N ζ hζ ha ha (hex _ hmem).choose_spec hslot).mpr ⟨rfl, Nat.mod_modEq _ _⟩

end WithChar

end CuspCountModC
p2m_reactivate "P2MW.S_ModularCurve_exists_slot_of_ord_jqModC_neg.CuspCountModC"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_slot_of_ord_jqModC_neg.CuspCountModC"

open ModularCurve AlgebraicCurve CuspCountModC in

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    (w : AlgebraicCurve.Place K ↥(modularFunctionFieldFullC K N))
    (hw : w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) < 0) :
    ∃ a b : ℕ, a ∣ N ∧ b < N / a ∧ Nat.gcd (Nat.gcd a b) (N / a) = 1 ∧
      ∃ (_ : NeZero a) (ι : ↥(modularFunctionFieldFullC K N) →ₐ[K] LaurentSeries K),
        ι ⟨jqModC K, jqModC_mem_full K N⟩ = qExpand K N (jqModC K) ∧
        ι ⟨qExpand K N (jqModC K), jqModCd_mem_full K N (dvd_refl N)⟩ =
            qExpand K (a * a) (qTwist (ζ ^ (b * a)) (jqModC K)) ∧
        ∀ x, w.ord x * ((a * Nat.gcd a (N / a) : ℕ) : ℤ) = (ι x).order := by
  haveI : NeZero (N : K) := ⟨hN⟩
  exact main_exhaustion K N ζ hζ w hw

end S_ModularCurve_exists_slot_of_ord_jqModC_neg
end P2MW
export P2MW.S_ModularCurve_exists_slot_of_ord_jqModC_neg (solution)
