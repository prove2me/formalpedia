-- Prove2me | solution 1 for ModularForm.exists_levelOne_esymm_qExpansion_congr_of_gamma0_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/7484db0e-807a-5147-a556-344050c5edd9

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularForm_heckeU_add_slash_fricke_eq_zero
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Theorems.Thm_ModularForm_exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_levelOne_esymm_qExpansion_congr_of_gamma0_two

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ModularForm
open UpperHalfPlane

noncomputable section

namespace P2mSolLevelOneEsymm

section Newton

variable {σ : Type*} [Fintype σ] {A B : Type*} [CommRing A] [CommRing B]

def esymmF (ρ : σ → A) (k : ℕ) : A :=
  MvPolynomial.aeval ρ (MvPolynomial.esymm σ ℤ k)

def psumF (ρ : σ → A) (k : ℕ) : A := ∑ i, ρ i ^ k

theorem aeval_psum (ρ : σ → A) (k : ℕ) :
    MvPolynomial.aeval ρ (MvPolynomial.psum σ ℤ k) = psumF ρ k := by
  simp [MvPolynomial.psum, psumF, map_sum]

@[scoped simp] theorem esymmF_zero (ρ : σ → A) : esymmF ρ 0 = 1 := by
  simp [esymmF, MvPolynomial.esymm_zero]

theorem newton [DecidableEq σ] (ρ : σ → A) (k : ℕ) :
    (k : A) * esymmF ρ k = (-1) ^ (k + 1) *
      ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 < k, (-1) ^ a.1 * esymmF ρ a.1 * psumF ρ a.2 := by
  have := congrArg (MvPolynomial.aeval ρ) (MvPolynomial.mul_esymm_eq_sum σ ℤ k)
  simpa [esymmF, aeval_psum, map_sum, map_mul, map_pow, map_neg] using this

theorem map_esymmF (f : A →+* B) (ρ : σ → A) (k : ℕ) :
    f (esymmF ρ k) = esymmF (fun i ↦ f (ρ i)) k := by
  exact MvPolynomial.comp_aeval_apply f.toIntAlgHom (f := ρ) (MvPolynomial.esymm σ ℤ k)

theorem esymmF_eq_multiset_esymm (ρ : σ → A) (k : ℕ) :
    esymmF ρ k = ((Finset.univ : Finset σ).val.map ρ).esymm k :=
  MvPolynomial.aeval_esymm_eq_multiset_esymm σ ℤ k ρ

theorem newton_unique {A : Type*} [CommRing A] (x y s : ℕ → A)
    (hreg : ∀ k : ℕ, 0 < k → ∀ b c : A, (k : A) * b = (k : A) * c → b = c)
    (h0 : x 0 = y 0)
    (hx : ∀ k : ℕ, (k : A) * x k = (-1) ^ (k + 1) *
      ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 < k, (-1) ^ a.1 * x a.1 * s a.2)
    (hy : ∀ k : ℕ, (k : A) * y k = (-1) ^ (k + 1) *
      ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 < k, (-1) ^ a.1 * y a.1 * s a.2) (k : ℕ) :
    x k = y k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact h0
    · refine hreg k hk _ _ ?_
      rw [hx, hy]
      congr 1
      refine Finset.sum_congr rfl fun a ha ↦ ?_
      simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
      rw [ih a.1 ha.2]

end Newton

section Multiset

variable {A : Type*} [CommRing A]

theorem esymm_cons_succ (a : A) (s : Multiset A) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_def, Multiset.prod_cons]
  rw [Multiset.sum_map_mul_left]

theorem esymm_replicate (c : A) (m n : ℕ) :
    (Multiset.replicate m c).esymm n = (m.choose n : A) * c ^ n := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n => simp [Multiset.esymm]
  | succ m ih =>
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n =>
      rw [Multiset.replicate_succ, esymm_cons_succ, ih, ih, Nat.choose_succ_succ, Nat.cast_add]
      ring

theorem esymm_cons_replicate (a c : A) (m : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (a ::ₘ Multiset.replicate m c).esymm n =
      (m.choose n : A) * c ^ n + a * ((m.choose (n - 1) : A) * c ^ (n - 1)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [esymm_cons_succ, esymm_replicate, esymm_replicate, Nat.add_sub_cancel]

theorem esymmF_option_const (p : ℕ) (b : ℤ) {r : ℕ} (hr : 1 ≤ r) :
    esymmF (fun i : Option (Fin p) ↦ Option.elim i ((p : ℤ) * b) fun _ ↦ -b) r =
      (-b) ^ r * ((p.choose r : ℤ) - p * (p.choose (r - 1) : ℤ)) := by
  rw [esymmF_eq_multiset_esymm]
  have : (Finset.univ : Finset (Option (Fin p))).val =
      none ::ₘ ((Finset.univ : Finset (Fin p)).val.map some) := rfl
  rw [this, Multiset.map_cons, Multiset.map_map, Function.comp_def]
  simp only [Option.elim]
  rw [Multiset.map_const', Finset.card_val, Finset.card_univ, Fintype.card_fin,
    esymm_cons_replicate _ _ _ hr]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hr
  simp only [Nat.add_sub_cancel, pow_succ]
  ring

end Multiset

section Formal

open PowerSeries

variable {R S : Type*} [CommRing R] [CommRing S]

def Useries (p : ℕ) (D : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n ↦ PowerSeries.coeff (n * p) D

@[scoped simp] theorem coeff_Useries (p : ℕ) (D : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (Useries p D) = PowerSeries.coeff (n * p) D := by
  simp [Useries]

theorem map_Useries (f : R →+* S) (p : ℕ) (D : PowerSeries R) :
    (Useries p D).map f = Useries p (D.map f) := by
  ext n; simp [coeff_map]

theorem rescale_C_eq (a c : R) : rescale a (C c) = C c := by
  ext n
  rw [coeff_rescale, coeff_C]
  split_ifs with h
  · simp [h]
  · simp

theorem sum_rescale_eq {K : Type*} [Field K] {p : ℕ} (hp : p.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (D : PowerSeries K) :
    ∑ j ∈ Finset.range p, rescale (ζ ^ j) D = p • expand p hp.ne_zero (Useries p D) := by
  ext m
  rw [map_sum, map_nsmul, coeff_expand]
  simp only [coeff_rescale]
  rw [← Finset.sum_mul]
  simp_rw [← pow_mul, fun j ↦ mul_comm j m, pow_mul]
  by_cases hm : p ∣ m
  · rw [(hζ.pow_eq_one_iff_dvd m).2 hm, if_pos hm, coeff_Useries, Nat.div_mul_cancel hm]
    simp
  · rw [if_neg hm, (hζ.pow_of_coprime m ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm).geom_sum_eq_zero
      hp.one_lt]
    simp

end Formal

abbrev Γ (p : ℕ) : Subgroup (GL (Fin 2) ℝ) := (CongruenceSubgroup.Gamma0 p : Subgroup SL(2, ℤ))

theorem one_mem_strictPeriods_Γ (p : ℕ) : (1 : ℝ) ∈ (Γ p).strictPeriods := by simp

theorem one_mem_strictPeriods_SL : (1 : ℝ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

def fricke (p : ℕ) (hp : p ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, -1; (p : ℝ), 0]
    (by rw [Matrix.det_fin_two_of]; simpa using hp)

theorem coe_fricke (p : ℕ) (hp : p ≠ 0) :
    ((fricke p hp : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0] := rfl

theorem abs_det_fricke (p : ℕ) (hp : p ≠ 0) : |(((fricke p hp).det : ℝˣ) : ℝ)| = p := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_fricke, Matrix.det_fin_two_of]
  simp

def frickeConj (p : ℕ) (g : SL(2, ℤ)) (hg : (p : ℤ) ∣ g 1 0) : SL(2, ℤ) :=
  ⟨!![g 1 1, -(g 1 0 / p); -(p * g 0 1), g 0 0], by
    have hdet := Matrix.det_fin_two g.1
    rw [g.2] at hdet
    rw [Matrix.det_fin_two_of]
    have := Int.ediv_mul_cancel hg
    linear_combination (-1 : ℤ) * hdet - (g 0 1) * this⟩

theorem frickeConj_mem (p : ℕ) (g : SL(2, ℤ)) (hg : (p : ℤ) ∣ g 1 0) :
    frickeConj p g hg ∈ CongruenceSubgroup.Gamma0 p := by
  rw [CongruenceSubgroup.Gamma0_mem]
  show (((!![g 1 1, -(g 1 0 / p); -(p * g 0 1), g 0 0] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) :
    ZMod p) = 0
  simp

theorem fricke_mul_mapGL (p : ℕ) (W : GL (Fin 2) ℝ)
    (hW : ((W : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0])
    (g : SL(2, ℤ)) (hg : (p : ℤ) ∣ g 1 0) :
    W * (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) =
      (Matrix.SpecialLinearGroup.mapGL ℝ (frickeConj p g hg) : GL (Fin 2) ℝ) * W := by
  have hc : (((g 1 0 / p : ℤ) : ℝ)) * (p : ℝ) = ((g 1 0 : ℤ) : ℝ) := by
    exact_mod_cast Int.ediv_mul_cancel hg
  ext i k
  rw [Units.val_mul, Units.val_mul, hW, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, frickeConj] <;> linarith [hc]

open ConjAct Pointwise in
theorem le_conj (p : ℕ) (W : GL (Fin 2) ℝ)
    (hW : ((W : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0]) :
    Γ p ≤ toConjAct W⁻¹ • Γ p := by
  rintro x ⟨g, hg, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← toConjAct_inv, inv_inv, toConjAct_smul]
  have hg' : (p : ℤ) ∣ g 1 0 := by
    have := (CongruenceSubgroup.Gamma0_mem (N := p) (A := g)).mp hg
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  rw [fricke_mul_mapGL p W hW g hg', mul_assoc, mul_inv_cancel, mul_one]
  exact ⟨_, frickeConj_mem p g hg', rfl⟩

open ConjAct Pointwise in

def slashFricke (p : ℕ) (f : ModularForm (Γ p) 2) (W : GL (Fin 2) ℝ)
    (hW : ((W : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0]) :
    ModularForm (Γ p) 2 where
  toFun := ⇑f ∣[(2 : ℤ)] W
  slash_action_eq' γ hγ := (ModularForm.translate f W).slash_action_eq' γ (le_conj p W hW hγ)
  holo' := (ModularForm.translate f W).holo'
  bdd_at_cusps' hc := (ModularForm.translate f W).bdd_at_cusps' (hc.mono (le_conj p W hW))

theorem coe_slashFricke (p : ℕ) (f : ModularForm (Γ p) 2) (W : GL (Fin 2) ℝ)
    (hW : ((W : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0]) :
    ⇑(slashFricke p f W hW) = ⇑f ∣[(2 : ℤ)] W := rfl

def IsMF (k : ℤ) (f : ℍ → ℂ) : Prop := ∃ F : ModularForm 𝒮ℒ k, ⇑F = f

namespace IsMF

variable {a b k : ℤ} {f g : ℍ → ℂ}

theorem zero : IsMF k 0 := ⟨0, rfl⟩

theorem one : IsMF 0 1 := ⟨1, rfl⟩

theorem add (hf : IsMF k f) (hg : IsMF k g) : IsMF k (f + g) := by
  obtain ⟨F, rfl⟩ := hf; obtain ⟨G, rfl⟩ := hg; exact ⟨F + G, rfl⟩

theorem neg (hf : IsMF k f) : IsMF k (-f) := by
  obtain ⟨F, rfl⟩ := hf; exact ⟨-F, rfl⟩

theorem smul (c : ℂ) (hf : IsMF k f) : IsMF k (c • f) := by
  obtain ⟨F, rfl⟩ := hf; exact ⟨c • F, rfl⟩

theorem mul (hf : IsMF a f) (hg : IsMF b g) : IsMF (a + b) (f * g) := by
  obtain ⟨F, rfl⟩ := hf; obtain ⟨G, rfl⟩ := hg; exact ⟨F.mul G, rfl⟩

theorem pow (hf : IsMF k f) (n : ℕ) : IsMF (n * k) (f ^ n) := by
  obtain ⟨F, rfl⟩ := hf; exact ⟨F.pow n, ModularForm.coe_pow F n⟩

theorem cast (h : a = b) (hf : IsMF a f) : IsMF b f := h ▸ hf

theorem sum {ι : Type*} (s : Finset ι) (f : ι → ℍ → ℂ) (h : ∀ i ∈ s, IsMF k (f i)) :
    IsMF k (∑ i ∈ s, f i) :=
  Finset.sum_induction f (IsMF k) (fun _ _ ↦ IsMF.add) IsMF.zero h

theorem neg_one_pow (n : ℕ) : IsMF 0 ((-1 : ℍ → ℂ) ^ n) :=
  ((IsMF.one.neg).pow n).cast (by simp)

theorem analytic (hf : IsMF k f) : AnalyticAt ℂ (cuspFunction 1 f) 0 := by
  obtain ⟨F, rfl⟩ := hf
  exact ModularFormClass.analyticAt_cuspFunction_zero F one_pos one_mem_strictPeriods_SL

theorem qExpansion_sum {ι : Type*} (s : Finset ι) (f : ι → ℍ → ℂ) (h : ∀ i ∈ s, IsMF k (f i)) :
    qExpansion 1 (∑ i ∈ s, f i) = ∑ i ∈ s, qExpansion 1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qExpansion_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      qExpansion_add (h a (Finset.mem_insert_self a s)).analytic
        (IsMF.sum s f fun i hi ↦ h i (Finset.mem_insert_of_mem hi)).analytic,
      ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)]

end IsMF

section Analytic

variable (p : ℕ) [hp : Fact p.Prime]

theorem p_ne_zero : p ≠ 0 := hp.out.ne_zero

abbrev Wp : GL (Fin 2) ℝ := fricke p (p_ne_zero p)

def kForm (h : ModularForm (Γ p) 2) : ModularForm (Γ p) 2 :=
  slashFricke p h (Wp p) (coe_fricke _ _)

theorem kForm_eq_slash (h : ModularForm (Γ p) 2) : ⇑(kForm p h) = ⇑h ∣[(2 : ℤ)] (Wp p) := rfl

theorem coe_kForm (h : ModularForm (Γ p) 2) : ⇑(kForm p h) = -ModularForm.heckeU 2 p ⇑h := by
  have := ModularForm.heckeU_add_slash_fricke_eq_zero p h (Wp p) (coe_fricke _ _)
  rw [kForm, coe_slashFricke]
  exact eq_neg_of_add_eq_zero_right this

def Cser (B : PowerSeries ℤ) : PowerSeries ℤ := PowerSeries.mk fun n ↦ -PowerSeries.coeff (n * p) B

def Sser (B : PowerSeries ℤ) (b : ℕ) : PowerSeries ℤ :=
  (p ^ b) • B ^ b + p • Useries p (Cser p B ^ b)

theorem qExpansion_kForm (h : ModularForm (Γ p) 2) {B : PowerSeries ℤ}
    (hB : B.map (Int.castRingHom ℂ) = qExpansion 1 ⇑h) :
    (Cser p B).map (Int.castRingHom ℂ) = qExpansion 1 ⇑(kForm p h) := by
  have hΓ := one_mem_strictPeriods_Γ p
  have hneg : ModularForm.heckeU 2 p ⇑h = -⇑(kForm p h) := by
    rw [coe_kForm, neg_neg]
  ext n
  have h1 := ModularFormClass.qCoeff_heckeU h hΓ (p_ne_zero p) n
  rw [ModularForm.coeffHeckeU_apply, ModularFormClass.qCoeff, ModularFormClass.qCoeff, hneg,
    ModularForm.qExpansion_neg one_pos hΓ (kForm p h), map_neg, ← hB, PowerSeries.coeff_map] at h1
  rw [PowerSeries.coeff_map, Cser, PowerSeries.coeff_mk, map_neg, ← h1, neg_neg]

def kAt (h : ModularForm (Γ p) 2) (j : ℕ) : ℍ → ℂ :=
  fun τ ↦ (kForm p h) (ModularForm.heckeMatrix p j • τ)

def rho (h : ModularForm (Γ p) 2) : Option (Fin p) → ℍ → ℂ :=
  fun i ↦ Option.elim i ((p : ℂ) • ⇑h) fun j ↦ kAt p h j

theorem psumF_rho (h : ModularForm (Γ p) 2) (b : ℕ) :
    psumF (rho p h) b = ((p : ℂ) • ⇑h) ^ b + ∑ j ∈ Finset.range p, kAt p h j ^ b := by
  rw [psumF, Fintype.sum_option]
  simp only [rho, Option.elim]
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ kAt p h j ^ b) p]

theorem pow_slash_fricke (h : ModularForm (Γ p) 2) (b : ℕ) :
    ((⇑h) ^ (b + 1)) ∣[(2 : ℤ) * ((b + 1 : ℕ) : ℤ)] (Wp p) =
      (p : ℂ) ^ b • (⇑(kForm p h)) ^ (b + 1) := by
  induction b with
  | zero =>
    simp only [zero_add, pow_one, Nat.cast_one, mul_one, pow_zero, one_smul]
    rfl
  | succ b ih =>
    have hw : (2 : ℤ) * ((b + 1 + 1 : ℕ) : ℤ) = 2 * ((b + 1 : ℕ) : ℤ) + 2 := by push_cast; ring
    rw [pow_succ, hw, ModularForm.mul_slash, ih, abs_det_fricke, ← kForm_eq_slash,
      pow_succ _ (b + 1), pow_succ]
    ext τ
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    ring

theorem isMF_psumF_succ (h : ModularForm (Γ p) 2) (b : ℕ) :
    IsMF ((2 : ℤ) * ((b + 1 : ℕ) : ℤ)) (psumF (rho p h) (b + 1)) := by
  obtain ⟨Y, hY⟩ := ModularForm.exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke p
    ((2 : ℤ) * ((b + 1 : ℕ) : ℤ)) ((h.pow (b + 1)).mcast (by push_cast; ring)) (Wp p)
    (coe_fricke _ _)
  refine ⟨((p : ℂ) ^ (b + 1) / (p : ℂ) ^ (2 * b)) • Y, ?_⟩
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (p_ne_zero p)
  have hz : (p : ℂ) ^ ((2 : ℤ) * ((b + 1 : ℕ) : ℤ) - 2) = (p : ℂ) ^ (2 * b) := by
    rw [show (2 : ℤ) * ((b + 1 : ℕ) : ℤ) - 2 = ((2 * b : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  rw [ModularForm.IsGLPos.coe_smul, hY, ModularForm.coe_mcast, ModularForm.coe_pow,
    pow_slash_fricke, ModularForm.heckeU_smul, hz, psumF_rho]
  ext τ
  simp only [Pi.smul_apply, Pi.add_apply, Pi.pow_apply, smul_eq_mul, Finset.sum_apply,
    ModularForm.heckeU_apply _ (p_ne_zero p), kAt]
  field_simp
  ring

theorem isMF_psumF (h : ModularForm (Γ p) 2) {b : ℕ} (hb : 1 ≤ b) :
    IsMF ((2 : ℤ) * (b : ℤ)) (psumF (rho p h) b) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le' hb
  exact isMF_psumF_succ p h c

theorem isMF_esymmF (h : ModularForm (Γ p) 2) (k : ℕ) :
    IsMF ((2 : ℤ) * (k : ℤ)) (esymmF (rho p h) k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [esymmF_zero]; exact IsMF.one.cast (by simp)
    · classical
      have hN := newton (rho p h) k
      have hS : IsMF ((2 : ℤ) * (k : ℤ)) ((-1) ^ (k + 1) *
          ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 < k,
            (-1) ^ a.1 * esymmF (rho p h) a.1 * psumF (rho p h) a.2) := by
        refine ((IsMF.neg_one_pow (k + 1)).mul
          (IsMF.sum (k := (2 : ℤ) * (k : ℤ)) _ _ fun a ha ↦ ?_)).cast (by simp)
        rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
        have h2 : 1 ≤ a.2 := by omega
        refine (((IsMF.neg_one_pow a.1).mul (ih a.1 ha.2)).mul (isMF_psumF p h h2)).cast ?_
        rw [← ha.1]; push_cast; ring
      have hE : esymmF (rho p h) k = (k : ℂ)⁻¹ • ((k : ℍ → ℂ) * esymmF (rho p h) k) := by
        ext τ
        simp only [Pi.smul_apply, Pi.mul_apply, Pi.natCast_apply, smul_eq_mul]
        rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hk.ne'), one_mul]
      rw [hE, hN]
      exact hS.smul _

theorem hasSum_of_isMF {k : ℤ} {Γ' : Subgroup (GL (Fin 2) ℝ)} [Γ'.IsArithmetic]
    (g : ModularForm Γ' k) (hΓ : (1 : ℝ) ∈ Γ'.strictPeriods) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (qExpansion 1 ⇑g).coeff m • Function.Periodic.qParam 1 τ ^ m) (g τ) :=
  hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex g hΓ)
    (ModularFormClass.holo g) (ModularFormClass.bdd_at_infty g) τ

def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)

theorem zeta_prim : IsPrimitiveRoot (zeta p) p := Complex.isPrimitiveRoot_exp p (p_ne_zero p)

theorem qParam_heckeMatrix_smul (j : ℕ) (τ : ℍ) :
    Function.Periodic.qParam 1 (ModularForm.heckeMatrix p j • τ : ℍ) =
      zeta p ^ j * Function.Periodic.qParam p τ := by
  simp only [Function.Periodic.qParam, zeta]
  rw [ModularForm.coe_heckeMatrix_smul (p_ne_zero p), ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

theorem qParam_p_pow (τ : ℍ) :
    Function.Periodic.qParam p τ ^ p = Function.Periodic.qParam 1 τ := by
  simp only [Function.Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (p_ne_zero p)
  push_cast
  field_simp

theorem hasSum_twist {D : PowerSeries ℂ} {g : ℍ → ℂ}
    (hg : ∀ τ : ℍ, HasSum (fun m : ℕ ↦ D.coeff m • Function.Periodic.qParam 1 τ ^ m) (g τ))
    (τ : ℍ) :
    HasSum (fun n : ℕ ↦ ((p : ℂ) * D.coeff (n * p)) • Function.Periodic.qParam 1 τ ^ n)
      (∑ j ∈ Finset.range p, g (ModularForm.heckeMatrix p j • τ)) := by
  have hpr : (Fact.out : p.Prime) = hp.out := rfl
  set q := Function.Periodic.qParam p τ with hq

  have h1 : HasSum (fun m : ℕ ↦ (∑ j ∈ Finset.range p, zeta p ^ (j * m)) * (D.coeff m * q ^ m))
      (∑ j ∈ Finset.range p, g (ModularForm.heckeMatrix p j • τ)) := by
    have := hasSum_sum (s := Finset.range p)
      (f := fun (j : ℕ) (m : ℕ) ↦ zeta p ^ (j * m) * (D.coeff m * q ^ m))
      (a := fun j ↦ g (ModularForm.heckeMatrix p j • τ)) (fun j _ ↦ by
        have := hg (ModularForm.heckeMatrix p j • τ)
        simp_rw [qParam_heckeMatrix_smul, mul_pow, ← pow_mul, smul_eq_mul] at this
        convert this using 1
        funext m; ring)
    convert this using 1
    funext m
    rw [Finset.sum_mul]

  have h2 : ∀ m : ℕ, (∑ j ∈ Finset.range p, zeta p ^ (j * m)) * (D.coeff m * q ^ m) =
      if p ∣ m then (p : ℂ) * (D.coeff m * q ^ m) else 0 := by
    intro m
    simp_rw [fun j ↦ mul_comm j m, pow_mul]
    by_cases hm : p ∣ m
    · rw [((zeta_prim p).pow_eq_one_iff_dvd m).2 hm, if_pos hm]
      simp
    · rw [if_neg hm, ((zeta_prim p).pow_of_coprime m
        ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm).symm).geom_sum_eq_zero hp.out.one_lt]
      simp
  simp_rw [h2] at h1

  have h3 := (Function.Injective.hasSum_iff (mul_left_injective₀ (p_ne_zero p))
    (f := fun m : ℕ ↦ if p ∣ m then (p : ℂ) * (D.coeff m * q ^ m) else 0)
    (a := ∑ j ∈ Finset.range p, g (ModularForm.heckeMatrix p j • τ)) (fun m hm ↦ by
      rw [if_neg]
      rintro ⟨c, rfl⟩
      exact hm ⟨c, mul_comm c p⟩)).2 h1
  convert h3 using 1
  funext n
  simp only [Function.comp_apply, smul_eq_mul, hq]
  rw [if_pos ⟨n, mul_comm n p⟩, pow_mul', qParam_p_pow]
  ring

theorem qExpansion_psumF (h : ModularForm (Γ p) 2) {B : PowerSeries ℤ}
    (hB : B.map (Int.castRingHom ℂ) = qExpansion 1 ⇑h) (b : ℕ) (hb : 1 ≤ b) :
    qExpansion 1 (psumF (rho p h) b) = (Sser p B b).map (Int.castRingHom ℂ) := by
  obtain ⟨Z, hZ⟩ := isMF_psumF p h hb
  rw [← hZ]
  have hΓ := one_mem_strictPeriods_Γ p

  have hA : ∀ τ : ℍ, HasSum (fun m : ℕ ↦ ((p : ℂ) ^ b * (B ^ b).coeff m : ℂ) •
      Function.Periodic.qParam 1 τ ^ m) ((((p : ℂ) • ⇑h) ^ b) τ) := by
    intro τ
    have := (hasSum_of_isMF (h.pow b) hΓ τ).mul_left ((p : ℂ) ^ b)
    rw [ModularForm.qExpansion_pow one_pos hΓ, ← hB, ← map_pow] at this
    simp only [PowerSeries.coeff_map, eq_intCast, ModularForm.coe_pow, Pi.pow_apply] at this
    convert this using 1 <;> try rfl
    · funext m; simp only [smul_eq_mul]; ring
    · simp [mul_pow]

  have hK : ∀ τ : ℍ, HasSum (fun m : ℕ ↦ ((Cser p B ^ b).map (Int.castRingHom ℂ)).coeff m •
      Function.Periodic.qParam 1 τ ^ m) (((⇑(kForm p h)) ^ b) τ) := by
    intro τ
    have := hasSum_of_isMF ((kForm p h).pow b) hΓ τ
    rwa [ModularForm.qExpansion_pow one_pos hΓ, ← qExpansion_kForm p h hB, ← map_pow,
      ModularForm.coe_pow] at this
  have hT := hasSum_twist p hK
  symm
  ext m
  simp only [PowerSeries.coeff_map]
  refine ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_SL (f := Z)
    (c := fun m ↦ Int.castRingHom ℂ (PowerSeries.coeff m (Sser p B b))) ?_ m
  intro τ
  rw [hZ, psumF_rho, Pi.add_apply, Finset.sum_apply]
  have := (hA τ).add (hT τ)
  simp only [Pi.pow_apply, kAt] at this ⊢
  convert this using 1
  funext n
  simp only [Sser, map_add, map_nsmul, coeff_Useries, PowerSeries.coeff_map, eq_intCast]
  simp only [smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

end Analytic

section FormalModel

open PowerSeries

variable {R S : Type*} [CommRing R] [CommRing S]
variable (p : ℕ) [hp : Fact p.Prime] (B : PowerSeries ℤ)

abbrev OO : Subalgebra ℤ ℂ := integralClosure ℤ ℂ

noncomputable def zetaO : OO := ⟨zeta p, (zeta_prim p).isIntegral (Fact.out : p.Prime).pos⟩

noncomputable def rootO : Option (Fin p) → PowerSeries OO := fun i ↦
  Option.elim i (p • expand p (p_ne_zero p) (B.map (algebraMap ℤ OO)))
    fun j ↦ rescale (zetaO p ^ (j : ℕ)) ((Cser p B).map (algebraMap ℤ OO))

noncomputable def rootC : Option (Fin p) → PowerSeries ℂ := fun i ↦
  (rootO p B i).map (algebraMap OO ℂ)

theorem algebraMap_OO_comp : (algebraMap OO ℂ).comp (algebraMap ℤ OO) = Int.castRingHom ℂ :=
  RingHom.ext_int _ _

theorem map_map_OO (D : PowerSeries ℤ) :
    (D.map (algebraMap ℤ OO)).map (algebraMap OO ℂ) = D.map (Int.castRingHom ℂ) := by
  rw [← algebraMap_OO_comp, PowerSeries.map_comp]; rfl

theorem rootC_none :
    rootC p B none = p • expand p (p_ne_zero p) (B.map (Int.castRingHom ℂ)) := by
  simp only [rootC, rootO, Option.elim, map_nsmul]
  rw [map_expand, map_map_OO]

theorem rootC_some (j : Fin p) :
    rootC p B (some j) = rescale (zeta p ^ (j : ℕ)) ((Cser p B).map (Int.castRingHom ℂ)) := by
  simp only [rootC, rootO, Option.elim]
  rw [← rescale_map, map_map_OO, map_pow]
  rfl

theorem psumF_rootC (b : ℕ) :
    psumF (rootC p B) b = expand p (p_ne_zero p) ((Sser p B b).map (Int.castRingHom ℂ)) := by
  rw [psumF, Fintype.sum_option, rootC_none]
  simp_rw [rootC_some]
  rw [Fin.sum_univ_eq_sum_range
    (fun j ↦ rescale (zeta p ^ j) ((Cser p B).map (Int.castRingHom ℂ)) ^ b) p]
  simp_rw [← map_pow]
  rw [sum_rescale_eq (Fact.out : p.Prime) (zeta_prim p)]
  simp only [Sser, map_add, map_nsmul, map_pow, map_Useries, smul_pow]

set_option synthInstance.maxHeartbeats 800000

variable (M : ℤ)

abbrev OOmod := OO ⧸ Ideal.span {(M : OO)}

abbrev red : OO →+* OOmod M := Ideal.Quotient.mk _

theorem red_M_mul (t : OO) : red M ((M : OO) * t) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

variable {B M} in
theorem map_red_B (hdvd : ∀ n : ℕ, 1 ≤ n → M ∣ B.coeff n) :
    (B.map (algebraMap ℤ OO)).map (red M) =
      C ((red M) (algebraMap ℤ OO (B.coeff 0))) := by
  ext n
  rw [coeff_map, coeff_map, coeff_C]
  split_ifs with hn
  · rw [hn]
  · obtain ⟨t, ht⟩ := hdvd n (Nat.one_le_iff_ne_zero.2 hn)
    rw [ht, map_mul, eq_intCast, red_M_mul]

variable {B M} in
theorem map_red_Cser (hdvd : ∀ n : ℕ, 1 ≤ n → M ∣ B.coeff n) :
    ((Cser p B).map (algebraMap ℤ OO)).map (red M) =
      C ((red M) (algebraMap ℤ OO (-B.coeff 0))) := by
  ext n
  rw [coeff_map, coeff_map, coeff_C, Cser, coeff_mk]
  split_ifs with hn
  · simp [hn]
  · obtain ⟨t, ht⟩ := hdvd (n * p) (Nat.one_le_iff_ne_zero.2 (mul_ne_zero hn (p_ne_zero p)))
    rw [ht, map_neg, map_neg, map_mul, eq_intCast, red_M_mul, neg_zero]

def rootVal : Option (Fin p) → ℤ := fun i ↦ Option.elim i ((p : ℤ) * B.coeff 0) fun _ ↦ -B.coeff 0

variable {B M} in
theorem map_red_rootO (hdvd : ∀ n : ℕ, 1 ≤ n → M ∣ B.coeff n) (i : Option (Fin p)) :
    (rootO p B i).map (red M) = C ((red M) (algebraMap ℤ OO (rootVal p B i))) := by
  cases i with
  | none =>
    simp only [rootO, rootVal, Option.elim, map_nsmul]
    rw [map_expand, map_red_B hdvd, expand_C, map_mul, map_natCast, map_mul, map_natCast,
      map_mul, map_natCast, nsmul_eq_mul]
  | some j =>
    simp only [rootO, rootVal, Option.elim]
    rw [← rescale_map, map_red_Cser p hdvd, rescale_C_eq]

variable {B M} in

theorem esymmF_rootO_modEq (hdvd : ∀ n : ℕ, 1 ≤ n → M ∣ B.coeff n) (k m : ℕ) :
    ∃ y : OO, PowerSeries.coeff m (esymmF (rootO p B) k) =
      PowerSeries.coeff m (C (algebraMap ℤ OO (esymmF (rootVal p B) k))) + (M : OO) * y := by
  have h1 : (esymmF (rootO p B) k).map (red M) =
      (C (algebraMap ℤ OO (esymmF (rootVal p B) k))).map (red M) := by
    rw [map_esymmF]
    simp_rw [map_red_rootO p hdvd]
    have h3 : ∀ x, C ((red M) ((algebraMap ℤ OO) x)) =
        ((C : OOmod M →+* PowerSeries (OOmod M)).comp ((red M).comp (algebraMap ℤ OO))) x :=
      fun x ↦ rfl
    simp_rw [map_C, h3]
    rw [map_esymmF ((C : OOmod M →+* PowerSeries (OOmod M)).comp ((red M).comp (algebraMap ℤ OO)))]
  have h2 := PowerSeries.ext_iff.1 h1 m
  rw [coeff_map, coeff_map, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton'] at h2
  obtain ⟨y, hy⟩ := h2
  exact ⟨y, by rw [mul_comm, hy]; ring⟩

theorem int_dvd_of_eq_mul {z N : ℤ} {y : ℂ} (hy : IsIntegral ℤ y) (h : (z : ℂ) = N * y) : N ∣ z := by
  by_cases hN : N = 0
  · subst hN
    have : (z : ℂ) = 0 := by simpa using h
    exact ⟨0, by exact_mod_cast this⟩
  · have hy' : y = algebraMap ℚ ℂ ((z : ℚ) / N) := by
      have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
      rw [eq_ratCast]; push_cast
      rw [eq_div_iff hN', mul_comm, ← h]
    rw [hy'] at hy
    have hint : IsIntegral ℤ ((z : ℚ) / N) :=
      (isIntegral_algHom_iff (algebraMap ℚ ℂ).toIntAlgHom (algebraMap ℚ ℂ).injective).1 hy
    obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨w, ?_⟩
    have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
    have : (w : ℚ) * N = z := by
      rw [eq_intCast] at hw
      rw [hw, div_mul_cancel₀ _ hN']
    exact_mod_cast (by rw [← this, mul_comm] : (z : ℚ) = N * w)

theorem exists_int_of_isIntegral {q : ℚ} (hq : IsIntegral ℤ (algebraMap ℚ ℂ q)) :
    ∃ z : ℤ, (z : ℚ) = q := by
  have hint : IsIntegral ℤ q :=
    (isIntegral_algHom_iff (algebraMap ℚ ℂ).toIntAlgHom (algebraMap ℚ ℂ).injective).1 hq
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  exact ⟨w, by simpa using hw⟩

end FormalModel

section Assembly

variable (p : ℕ) [hp : Fact p.Prime]

def Phi (h : ModularForm (Γ p) 2) (k : ℕ) : PowerSeries ℂ := qExpansion 1 (esymmF (rho p h) k)

theorem Phi_zero (h : ModularForm (Γ p) 2) : Phi p h 0 = 1 := by
  rw [Phi, esymmF_zero]; exact UpperHalfPlane.qExpansion_one 1

theorem map_map_Q (D : PowerSeries ℤ) :
    (D.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) = D.map (Int.castRingHom ℂ) := by
  have hc : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := RingHom.ext_int _ _
  rw [← hc, PowerSeries.map_comp]; rfl

theorem newton_Phi (h : ModularForm (Γ p) 2) {B : PowerSeries ℤ}
    (hB : B.map (Int.castRingHom ℂ) = qExpansion 1 ⇑h) (k : ℕ) :
    (k : PowerSeries ℂ) * Phi p h k = (-1) ^ (k + 1) *
      ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 < k,
        (-1) ^ a.1 * Phi p h a.1 * (Sser p B a.2).map (Int.castRingHom ℂ) := by
  classical
  simp only [Phi]
  have hN := newton (rho p h) k
  have hL : ((k : ℍ → ℂ) * esymmF (rho p h) k) = (k : ℂ) • esymmF (rho p h) k := by
    ext τ; simp
  have hterm : ∀ a : ℕ × ℕ, (-1 : ℍ → ℂ) ^ a.1 * esymmF (rho p h) a.1 * psumF (rho p h) a.2 =
      ((-1 : ℂ) ^ a.1) • (esymmF (rho p h) a.1 * psumF (rho p h) a.2) := by
    intro a; ext τ; simp [mul_assoc]
  have hR : ((-1 : ℍ → ℂ) ^ (k + 1) * ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 < k,
      (-1) ^ a.1 * esymmF (rho p h) a.1 * psumF (rho p h) a.2) =
      ((-1 : ℂ) ^ (k + 1)) • ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 < k,
        ((-1 : ℂ) ^ a.1) • (esymmF (rho p h) a.1 * psumF (rho p h) a.2) := by
    rw [Finset.sum_congr rfl fun a _ ↦ hterm a]
    ext τ; simp
  rw [hL, hR] at hN
  have hmem : ∀ a ∈ Finset.filter (fun a ↦ a.1 < k) (Finset.HasAntidiagonal.antidiagonal k),
      a.1 < k ∧ 1 ≤ a.2 ∧ a.1 + a.2 = k := by
    intro a ha
    rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
    exact ⟨ha.2, by omega, ha.1⟩
  have hI : ∀ a ∈ Finset.filter (fun a ↦ a.1 < k) (Finset.HasAntidiagonal.antidiagonal k),
      IsMF ((2 : ℤ) * (k : ℤ)) (((-1 : ℂ) ^ a.1) • (esymmF (rho p h) a.1 * psumF (rho p h) a.2)) := by
    intro a ha
    obtain ⟨_, h2, h3⟩ := hmem a ha
    exact (((isMF_esymmF p h a.1).mul (isMF_psumF p h h2)).cast
      (by rw [← h3]; push_cast; ring)).smul _
  apply_fun qExpansion 1 at hN
  rw [qExpansion_smul (isMF_esymmF p h k).analytic, qExpansion_smul (IsMF.sum _ _ hI).analytic,
    IsMF.qExpansion_sum _ _ hI] at hN
  rw [← map_natCast (PowerSeries.C (R := ℂ)) k, ← PowerSeries.smul_eq_C_mul, hN,
    PowerSeries.smul_eq_C_mul, map_pow, map_neg, map_one]
  congr 1
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  obtain ⟨_, h2, _⟩ := hmem a ha
  rw [qExpansion_smul ((isMF_esymmF p h a.1).mul (isMF_psumF p h h2)).analytic,
    qExpansion_mul (isMF_esymmF p h a.1).analytic (isMF_psumF p h h2).analytic,
    qExpansion_psumF p h hB a.2 h2, PowerSeries.smul_eq_C_mul, map_pow, map_neg, map_one, mul_assoc]

theorem expand_Phi (h : ModularForm (Γ p) 2) {B : PowerSeries ℤ}
    (hB : B.map (Int.castRingHom ℂ) = qExpansion 1 ⇑h) (k : ℕ) :
    PowerSeries.expand p (p_ne_zero p) (Phi p h k) = esymmF (rootC p B) k := by
  classical
  refine newton_unique (fun k ↦ PowerSeries.expand p (p_ne_zero p) (Phi p h k))
    (esymmF (rootC p B)) (psumF (rootC p B)) ?_ ?_ ?_ ?_ k
  · intro k hk b c hbc
    rw [← map_natCast (PowerSeries.C (R := ℂ)) k] at hbc
    exact ((isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hk.ne')).map PowerSeries.C).mul_left_cancel hbc
  · simp only [Phi_zero, map_one, esymmF_zero]
  · intro k
    have := congrArg (PowerSeries.expand p (p_ne_zero p)) (newton_Phi p h hB k)
    rw [map_mul, map_natCast] at this
    rw [this, map_mul, map_pow, map_neg, map_one, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [map_mul, map_mul, map_pow, map_neg, map_one, psumF_rootC]
  · intro k; exact newton (rootC p B) k

theorem expand_Phi_eq_map (h : ModularForm (Γ p) 2) {B : PowerSeries ℤ}
    (hB : B.map (Int.castRingHom ℂ) = qExpansion 1 ⇑h) (k : ℕ) :
    PowerSeries.expand p (p_ne_zero p) (Phi p h k) =
      (esymmF (rootO p B) k).map (algebraMap OO ℂ) := by
  rw [expand_Phi p h hB, map_esymmF]; rfl

theorem Phi_mem_range (h : ModularForm (Γ p) 2) {B : PowerSeries ℤ}
    (hB : B.map (Int.castRingHom ℂ) = qExpansion 1 ⇑h) (k : ℕ) :
    Phi p h k ∈ (PowerSeries.map (algebraMap ℚ ℂ)).range := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    classical
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨1, by rw [map_one, Phi_zero]⟩
    · have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
      have hE : Phi p h k = PowerSeries.C ((k : ℂ)⁻¹) * ((k : PowerSeries ℂ) * Phi p h k) := by
        rw [← mul_assoc, ← map_natCast (PowerSeries.C (R := ℂ)) k, ← map_mul,
          inv_mul_cancel₀ hk', map_one, one_mul]
      rw [hE, newton_Phi p h hB k]
      refine mul_mem ⟨PowerSeries.C ((k : ℚ)⁻¹), ?_⟩ (mul_mem (pow_mem (neg_mem (one_mem _)) _)
        (sum_mem fun a ha ↦ ?_))
      · rw [PowerSeries.map_C, map_inv₀, map_natCast]
      · rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
        exact mul_mem (mul_mem (pow_mem (neg_mem (one_mem _)) _) (ih a.1 ha.2))
          ⟨(Sser p B a.2).map (Int.castRingHom ℚ), map_map_Q _⟩

theorem exists_intSeries (h : ModularForm (Γ p) 2) {B : PowerSeries ℤ}
    (hB : B.map (Int.castRingHom ℂ) = qExpansion 1 ⇑h) (k : ℕ) :
    ∃ T : PowerSeries ℤ, T.map (Int.castRingHom ℂ) = Phi p h k := by
  obtain ⟨t, ht⟩ := Phi_mem_range p h hB k
  have hint : ∀ n : ℕ, ∃ z : ℤ, (z : ℚ) = PowerSeries.coeff n t := by
    intro n
    apply exists_int_of_isIntegral
    have h1 : algebraMap ℚ ℂ (PowerSeries.coeff n t) = PowerSeries.coeff n (Phi p h k) := by
      rw [← ht, PowerSeries.coeff_map]
    have h2 : PowerSeries.coeff n (Phi p h k) =
        algebraMap OO ℂ (PowerSeries.coeff (p * n) (esymmF (rootO p B) k)) := by
      rw [← PowerSeries.coeff_map, ← expand_Phi_eq_map p h hB k, PowerSeries.coeff_expand_mul]
    rw [h1, h2]
    exact (PowerSeries.coeff (p * n) (esymmF (rootO p B) k)).2
  choose z hz using hint
  refine ⟨PowerSeries.mk z, ?_⟩
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, ← ht, PowerSeries.coeff_map, ← hz]
  simp

theorem esymmF_rootVal (B : PowerSeries ℤ) {r : ℕ} (hr : 1 ≤ r) :
    esymmF (rootVal p B) r =
      (-PowerSeries.constantCoeff B) ^ r * ((p.choose r : ℤ) - p * (p.choose (r - 1) : ℤ)) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact esymmF_option_const p (PowerSeries.coeff 0 B) hr

theorem main (h : ModularForm (Γ p) 2) {B : PowerSeries ℤ}
    (hB : B.map (Int.castRingHom ℂ) = qExpansion 1 ⇑h) (M : ℤ)
    (hdvd : ∀ n : ℕ, 1 ≤ n → M ∣ B.coeff n) {r : ℕ} (hr : 1 ≤ r) :
    ∃ (F : ModularForm 𝒮ℒ (2 * r)) (T : PowerSeries ℤ),
      T.map (Int.castRingHom ℂ) = qExpansion 1 ⇑F ∧
      (∀ n : ℕ, 1 ≤ n → M ∣ T.coeff n) ∧
      M ∣ PowerSeries.constantCoeff T -
        (-PowerSeries.constantCoeff B) ^ r * ((p.choose r : ℤ) - p * (p.choose (r - 1) : ℤ)) := by
  obtain ⟨F, hF⟩ := isMF_esymmF p h r
  obtain ⟨T, hT⟩ := exists_intSeries p h hB r
  have hΦ : ∀ m : ℕ, ∃ y : OO,
      (PowerSeries.coeff m (PowerSeries.expand p (p_ne_zero p) (Phi p h r)) : ℂ) =
        (if m = 0 then ((esymmF (rootVal p B) r : ℤ) : ℂ) else 0) + (M : ℂ) * (y : ℂ) := by
    intro m
    obtain ⟨y, hy⟩ := esymmF_rootO_modEq p hdvd r m
    refine ⟨y, ?_⟩
    rw [expand_Phi_eq_map p h hB, PowerSeries.coeff_map, hy, map_add, map_mul, PowerSeries.coeff_C]
    congr 1
    · split_ifs
      · exact congrFun (congrArg DFunLike.coe (algebraMap_OO_comp)) _
      · exact map_zero _
  refine ⟨F, T, by rw [hT, hF]; rfl, fun n hn ↦ ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hΦ (p * n)
    rw [if_neg (mul_ne_zero (p_ne_zero p) (by omega)), zero_add, PowerSeries.coeff_expand_mul,
      ← hT, PowerSeries.coeff_map, eq_intCast] at hy
    exact int_dvd_of_eq_mul y.2 hy
  · obtain ⟨y, hy⟩ := hΦ 0
    rw [if_pos rfl, PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_expand,
      ← hT, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, eq_intCast,
      esymmF_rootVal p B hr, PowerSeries.coeff_zero_eq_constantCoeff_apply] at hy
    refine int_dvd_of_eq_mul y.2 (y := (y : ℂ)) ?_
    push_cast at hy ⊢
    rw [hy]; ring

end Assembly

end P2mSolLevelOneEsymm
p2m_reactivate "P2MW.S_ModularForm_exists_levelOne_esymm_qExpansion_congr_of_gamma0_two.P2mSolLevelOneEsymm"

end
p2m_reactivate "P2MW.S_ModularForm_exists_levelOne_esymm_qExpansion_congr_of_gamma0_two.P2mSolLevelOneEsymm"

open scoped MatrixGroups

theorem solution (p : ℕ) [Fact p.Prime]
    (h : ModularForm (CongruenceSubgroup.Gamma0 p) 2) {B : PowerSeries ℤ}
    (hB : B.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 ⇑h) (M : ℤ)
    (hdvd : ∀ n : ℕ, 1 ≤ n → M ∣ B.coeff n) {r : ℕ} (hr : 1 ≤ r) :
    ∃ (F : ModularForm 𝒮ℒ (2 * r)) (T : PowerSeries ℤ),
      T.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 ⇑F ∧
      (∀ n : ℕ, 1 ≤ n → M ∣ T.coeff n) ∧
      M ∣ PowerSeries.constantCoeff T -
        (-PowerSeries.constantCoeff B) ^ r * ((p.choose r : ℤ) - p * (p.choose (r - 1) : ℤ)) :=
  P2mSolLevelOneEsymm.main p h hB M hdvd hr

end S_ModularForm_exists_levelOne_esymm_qExpansion_congr_of_gamma0_two
end P2MW
export P2MW.S_ModularForm_exists_levelOne_esymm_qExpansion_congr_of_gamma0_two (solution)
