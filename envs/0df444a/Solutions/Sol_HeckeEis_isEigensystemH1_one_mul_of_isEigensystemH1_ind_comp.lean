-- Prove2me | solution 1 for HeckeEis.isEigensystemH1_one_mul_of_isEigensystemH1_ind_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/1be09ea3-bc5d-50cd-9f5d-5df852d5808c

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCocycles
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries
import Theorems.Thm_HeckeEis_exists_addMonoidHom_functional_cocycle_smul_heckeOperatorHom_mul_eq
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_isEigensystemH1_one_mul_of_isEigensystemH1_ind_comp

set_option autoImplicit false

namespace ShapiroInd

open CongruenceSubgroup HeckeEis CuspidalType
open scoped MatrixGroups

section Induced

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable (N ℓ : ℕ) [NeZero ℓ] (ρ : Representation K (Gamma0 N) V) (a : V →ₗ[K] V)

def IsCompat : Prop :=
  ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a

noncomputable def heckeLin : (Gamma0 N → V) →ₗ[K] (Gamma0 N → V) where
  toFun := coeffHeckeFun N ℓ ρ a
  map_add' z w := by
    letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
    ext g
    simp only [coeffHeckeFun_apply, Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c z := by
    letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
    ext g
    simp only [coeffHeckeFun_apply, Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]

variable {N ℓ ρ a}

noncomputable def heckeZ1 (ha : IsCompat N ℓ ρ a) : ↥(coeffCocycles ρ) →ₗ[K] ↥(coeffCocycles ρ) :=
  (heckeLin N ℓ ρ a).restrict fun _ hz => coeffHeckeFun_mem_coeffCocycles N ℓ ρ a ha hz

@[scoped simp] theorem coe_heckeZ1 (ha : IsCompat N ℓ ρ a) (z : ↥(coeffCocycles ρ)) :
    (heckeZ1 ha z : Gamma0 N → V) = coeffHeckeFun N ℓ ρ a z := rfl

noncomputable def heckeH1 (ha : IsCompat N ℓ ρ a) : coeffH1 ρ →ₗ[K] coeffH1 ρ :=
  ((coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype).mapQ
    ((coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype) (heckeZ1 ha)
    fun _ hz => coeffHeckeFun_mem_coeffCoboundaries N ℓ ρ a ha hz

theorem heckeH1_mk (ha : IsCompat N ℓ ρ a) (z : ↥(coeffCocycles ρ)) :
    heckeH1 ha (coeffH1Mk ρ z) = coeffH1Mk ρ (heckeZ1 ha z) := rfl

theorem isCoeffHeckeOnH1_heckeH1 (ha : IsCompat N ℓ ρ a) : IsCoeffHeckeOnH1 N ℓ ρ a (heckeH1 ha) :=
  fun z => ⟨heckeZ1 ha z, rfl, rfl⟩

end Induced

section Twist

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable (N : ℕ) (ρ : Representation K (Gamma0 N) V)

theorem coeffHeckeFun_smul (ℓ : ℕ) [NeZero ℓ] (c : K) (a : V →ₗ[K] V) (z : Gamma0 N → V) :
    coeffHeckeFun N ℓ ρ (c • a) z = c • coeffHeckeFun N ℓ ρ a z := by
  letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  ext g
  simp only [coeffHeckeFun_apply, Pi.smul_apply, LinearMap.smul_apply, map_smul, Finset.smul_sum]

theorem smul_isCoeffHeckeOnH1 (ℓ : ℕ) [NeZero ℓ] (c : K) (a : V →ₗ[K] V)
    {T : coeffH1 ρ →ₗ[K] coeffH1 ρ} (hT : IsCoeffHeckeOnH1 N ℓ ρ a T) :
    IsCoeffHeckeOnH1 N ℓ ρ (c • a) (c • T) := by
  intro z
  obtain ⟨w, hw, hTw⟩ := hT z
  refine ⟨c • w, ?_, ?_⟩
  · rw [Submodule.coe_smul, hw, coeffHeckeFun_smul]
  · rw [LinearMap.smul_apply, hTw, map_smul]

theorem isEigensystemH1_of_smul (a a' : ℕ → (V →ₗ[K] V)) (χ : ℕ → K) (S₀ : Set ℕ) (lam : ℕ → K)
    (haa' : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → a' ℓ = χ ℓ • a ℓ)
    (h : IsEigensystemH1 N ρ a S₀ lam) :
    IsEigensystemH1 N ρ a' S₀ (fun ℓ => χ ℓ * lam ℓ) := by
  obtain ⟨x, hx, heig⟩ := h
  refine ⟨x, hx, fun ℓ hℓ hℓN hℓS => ?_⟩
  obtain ⟨T, hT, hTx⟩ := heig ℓ hℓ hℓN hℓS
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  refine ⟨χ ℓ • T, ?_, ?_⟩
  · have := smul_isCoeffHeckeOnH1 N ρ ℓ (χ ℓ) (a ℓ) hT
    rw [← haa' ℓ hℓ hℓN hℓS] at this
    exact this
  · rw [LinearMap.smul_apply, hTx, smul_smul]

theorem isEigensystemH1_congr (a : ℕ → (V →ₗ[K] V)) (S₀ : Set ℕ) {lam lam' : ℕ → K}
    (hll : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → lam ℓ = lam' ℓ) (h : IsEigensystemH1 N ρ a S₀ lam) :
    IsEigensystemH1 N ρ a S₀ lam' := by
  obtain ⟨x, hx, heig⟩ := h
  refine ⟨x, hx, fun ℓ hℓ hℓN hℓS => ?_⟩
  obtain ⟨T, hT, hTx⟩ := heig ℓ hℓ hℓN hℓS
  exact ⟨T, hT, by rw [hTx, hll ℓ hℓ hℓN hℓS]⟩

theorem isEigensystemH1_mono (a : ℕ → (V →ₗ[K] V)) {S₀ S₁ : Set ℕ} (hS : S₀ ⊆ S₁) {lam : ℕ → K}
    (h : IsEigensystemH1 N ρ a S₀ lam) : IsEigensystemH1 N ρ a S₁ lam := by
  obtain ⟨x, hx, heig⟩ := h
  exact ⟨x, hx, fun ℓ hℓ hℓN hℓS => heig ℓ hℓ hℓN fun h' => hℓS (hS h')⟩

end Twist

section PermModule

variable (N q : ℕ) [Fact q.Prime] (κ : Type*) [Field κ]

noncomputable def red : Gamma0 N →* GL2 q :=
  (Matrix.SpecialLinearGroup.toGL.comp (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype

theorem red_val (γ : Gamma0 N) :
    ((red N q γ : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) = ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod q)) :=
  rfl

noncomputable abbrev rhoP : Representation κ (Gamma0 N) (ProjLine q →₀ κ) := (ind q κ).comp (red N q)

noncomputable def aP (ℓ : ℕ) : (ProjLine q →₀ κ) →ₗ[κ] (ProjLine q →₀ κ) :=
  if h : ((ℓ : ZMod q) ≠ 0) then (ind q κ) (diagElem q (Units.mk0 (ℓ : ZMod q) h)) else LinearMap.id

theorem aP_of_ne (ℓ : ℕ) (h : (ℓ : ZMod q) ≠ 0) : aP q κ ℓ = (ind q κ) (diagElem q (Units.mk0 (ℓ : ZMod q) h)) :=
  dif_pos h

theorem ind_apply (g : GL2 q) (f : ProjLine q →₀ κ) (x : ProjLine q) :
    (ind q κ g f) x = f (g⁻¹ • x) :=
  Representation.ofMulActionFinsupp_apply g f x

def basePt : ProjLine q := Projectivization.mk (ZMod q) ![0, 1] (by simp)

noncomputable def evb : (ProjLine q →₀ κ) →ₗ[κ] κ := Finsupp.lapply (basePt q)

theorem toLin_smul_vec (g : GL2 q) (v : Fin 2 → ZMod q) :
    (Matrix.GeneralLinearGroup.toLin g) • v = (g : Matrix (Fin 2) (Fin 2) (ZMod q)).mulVec v := by
  show ((Matrix.GeneralLinearGroup.toLin g : LinearMap.GeneralLinearGroup (ZMod q) (Fin 2 → ZMod q)) :
      (Fin 2 → ZMod q) →ₗ[ZMod q] (Fin 2 → ZMod q)) v = _
  simp [Matrix.GeneralLinearGroup.toLin, Matrix.toLin'_apply]

theorem mulVec_ne_zero (g : GL2 q) {v : Fin 2 → ZMod q} (hv : v ≠ 0) :
    (g : Matrix (Fin 2) (Fin 2) (ZMod q)).mulVec v ≠ 0 := by
  rw [← toLin_smul_vec]
  exact (smul_ne_zero_iff_ne _).mpr hv

private theorem _root_.ShapiroInd.smul_mk (g : GL2 q) (v : Fin 2 → ZMod q) (hv : v ≠ 0) :
    g • Projectivization.mk (ZMod q) v hv =
      Projectivization.mk (ZMod q) ((g : Matrix (Fin 2) (Fin 2) (ZMod q)).mulVec v) (mulVec_ne_zero q g hv) := by
  show Matrix.GeneralLinearGroup.toLin g • Projectivization.mk (ZMod q) v hv = _
  rw [Projectivization.smul_mk]
  congr 1

p2m_export "ShapiroInd" "smul_mk"

theorem smul_basePt_eq_iff (g : GL2 q) : g • basePt q = basePt q ↔ (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1 = 0 := by
  rw [basePt, smul_mk, Projectivization.mk_eq_mk_iff]
  constructor
  · rintro ⟨a, ha⟩
    have h0 := congrFun ha 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
    exact h0.symm
  · intro h
    have hdet : ((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1) ≠ 0 := by
      intro h11
      have := g.isUnit.ne_zero
      have hd : (g : Matrix (Fin 2) (Fin 2) (ZMod q)).det = 0 := by
        rw [Matrix.det_fin_two, h, h11]; ring
      exact (Matrix.isUnit_iff_isUnit_det _ |>.mp g.isUnit).ne_zero hd
    refine ⟨Units.mk0 _ hdet, funext fun i => ?_⟩
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h]

theorem evb_comp_ind_of_smul_eq (g : GL2 q) (hg : g • basePt q = basePt q) : evb q κ ∘ₗ (ind q κ g) = evb q κ := by
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.comp_apply, evb, Finsupp.lapply_apply, Finsupp.lapply_apply, ind_apply]
  congr 1
  rw [← hg, inv_smul_smul, hg]

theorem evb_rhoP (δ : Gamma0 N) (hδ : (q : ℤ) ∣ (δ : SL(2, ℤ)) 0 1) :
    evb q κ ∘ₗ rhoP N q κ δ = evb q κ := by
  apply evb_comp_ind_of_smul_eq
  rw [smul_basePt_eq_iff, red_val, Matrix.map_apply]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hδ

theorem evb_aP (ℓ : ℕ) : evb q κ ∘ₗ aP q κ ℓ = (1 : κ) • evb q κ := by
  rw [one_smul]
  by_cases h : ((ℓ : ZMod q) ≠ 0)
  · rw [aP_of_ne q κ ℓ h]
    apply evb_comp_ind_of_smul_eq
    rw [smul_basePt_eq_iff]
    simp [diagElem]
  · rw [aP, dif_neg h]; rfl

theorem isCompat_P (ℓ : ℕ) [NeZero ℓ] (hℓ : (ℓ : ZMod q) ≠ 0) : IsCompat N ℓ (rhoP N q κ) (aP q κ ℓ) := by
  intro u
  rw [aP_of_ne q κ ℓ hℓ]
  show (ind q κ) (diagElem q (Units.mk0 (ℓ : ZMod q) hℓ)) ∘ₗ (ind q κ) (red N q (heckeConj N ℓ u)) =
    (ind q κ) (red N q (u : Gamma0 N)) ∘ₗ (ind q κ) (diagElem q (Units.mk0 (ℓ : ZMod q) hℓ))
  rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  obtain ⟨k, hk⟩ := (mem_heckeUpper N ℓ).mp u.2
  ext i j
  rw [Units.val_mul, Units.val_mul, red_val, red_val]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, diagElem, Matrix.map_apply, heckeConj, heckeConjSL, heckeConjMat, hk,
      Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr (NeZero.ne ℓ))] <;> ring

end PermModule

section Shapiro

variable (N q : ℕ) [Fact q.Prime] (κ : Type*) [Field κ]

theorem rhoP_apply (γ : Gamma0 N) (f : ProjLine q →₀ κ) (x : ProjLine q) :
    (rhoP N q κ γ f) x = f ((red N q γ)⁻¹ • x) :=
  ind_apply q κ _ f x

theorem cocycle_one' {z : Gamma0 N → (ProjLine q →₀ κ)} (hz : z ∈ coeffCocycles (rhoP N q κ)) : z 1 = 0 := by
  have h := hz 1 1
  rw [mul_one, map_one, Module.End.one_apply] at h
  have : z 1 + z 1 = z 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel this

theorem cocycle_inv' {z : Gamma0 N → (ProjLine q →₀ κ)} (hz : z ∈ coeffCocycles (rhoP N q κ)) (γ : Gamma0 N) :
    z γ⁻¹ = -(rhoP N q κ γ⁻¹ (z γ)) := by
  have h := hz γ⁻¹ γ
  rw [inv_mul_cancel, cocycle_one' N q κ hz] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem mem_coeffCoboundaries_of_forall_apply_basePt
    {z : Gamma0 N → (ProjLine q →₀ κ)} (hz : z ∈ coeffCocycles (rhoP N q κ))
    (s : ProjLine q → Gamma0 N) (hs : ∀ x, red N q (s x) • basePt q = x)
    (h0 : ∀ h : Gamma0 N, red N q h • basePt q = basePt q → z h (basePt q) = 0) :
    z ∈ coeffCoboundaries (rhoP N q κ) := by
  classical

  let F : ProjLine q →₀ κ := Finsupp.equivFunOnFinite.symm (fun x => z (s x) x)
  have hF : ∀ x, F x = z (s x) x := fun x => by simp [F]

  have hkey : ∀ γ : Gamma0 N, z γ (red N q γ • basePt q) = F (red N q γ • basePt q) := by
    intro γ
    set x := red N q γ • basePt q with hx
    set h : Gamma0 N := (s x)⁻¹ * γ with hh
    have hγ : γ = s x * h := by rw [hh, mul_inv_cancel_left]
    have hhx : red N q h • basePt q = basePt q := by
      rw [hh, map_mul, map_inv, mul_smul, inv_smul_eq_iff, hs]
    have hzh : z h (basePt q) = 0 := h0 h hhx
    rw [hF]
    conv_lhs => rw [hγ]
    rw [hz (s x) h, Finsupp.coe_add, Pi.add_apply, rhoP_apply]
    have : (red N q (s x))⁻¹ • x = basePt q := by rw [inv_smul_eq_iff, hs]
    rw [this, hzh, add_zero]
  refine (mem_coeffCoboundaries_iff _ _).mpr ⟨-F, funext fun γ => Finsupp.ext fun x => ?_⟩

  have hpt : (red N q γ)⁻¹ • x = red N q (γ⁻¹ * s x) • basePt q := by
    rw [map_mul, map_inv, mul_smul, hs]
  have hA : F ((red N q γ)⁻¹ • x) = z (γ⁻¹ * s x) ((red N q γ)⁻¹ • x) := by
    rw [hpt]; exact (hkey _).symm
  have hB : z (γ⁻¹ * s x) ((red N q γ)⁻¹ • x) = -(z γ x) + F x := by
    rw [hz γ⁻¹ (s x), Finsupp.coe_add, Pi.add_apply, cocycle_inv' N q κ hz γ, Finsupp.coe_neg, Pi.neg_apply,
      rhoP_apply, rhoP_apply, map_inv, inv_inv, smul_inv_smul, hF]
  show (rhoP N q κ γ (-F)) x - (-F) x = z γ x
  rw [map_neg, Finsupp.coe_neg, Pi.neg_apply, rhoP_apply, hA, hB, Finsupp.coe_neg, Pi.neg_apply]
  ring

def Tg : Gamma0 N := ⟨ModularGroup.T, by rw [Gamma0_mem, ModularGroup.T]; simp⟩

theorem coe_Tg_zpow (n : ℤ) : (((Tg N ^ n : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, n; 0, 1] := by
  rw [SubgroupClass.coe_zpow]
  show ((ModularGroup.T ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = _
  rw [ModularGroup.coe_T_zpow]

theorem red_mulVec_basePt (γ : Gamma0 N) :
    ((red N q γ : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)).mulVec ![0, 1] =
      ![(((γ : SL(2, ℤ)) 0 1 : ℤ) : ZMod q), (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod q)] := by
  rw [red_val]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply]

theorem exists_section (hqN : ¬ q ∣ N) : ∃ s : ProjLine q → Gamma0 N, ∀ x, red N q (s x) • basePt q = x := by
  classical
  have hq : q.Prime := Fact.out

  have hcop : IsCoprime (q : ℤ) (N : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact (Nat.Prime.coprime_iff_not_dvd hq).mpr hqN
  obtain ⟨u, v, huv⟩ := hcop
  have hvq : ((v : ℤ) : ZMod q) ≠ 0 := by
    intro hv0
    have h1 : (((u * q + v * N : ℤ)) : ZMod q) = 1 := by rw [huv]; simp
    push_cast at h1
    rw [hv0, ZMod.natCast_self, mul_zero, zero_mul, zero_add] at h1
    exact zero_ne_one h1

  let Winf : SL(2, ℤ) := ⟨!![u, -v; (N : ℤ), (q : ℤ)], by
    rw [Matrix.det_fin_two_of]; linear_combination huv⟩
  have hWinf : Winf ∈ Gamma0 N := by
    rw [Gamma0_mem]
    show ((((N : ℤ)) : ℤ) : ZMod N) = 0
    simp
  suffices h : ∀ x : ProjLine q, ∃ γ : Gamma0 N, red N q γ • basePt q = x from
    ⟨fun x => (h x).choose, fun x => (h x).choose_spec⟩
  intro x
  induction x using Projectivization.ind with
  | h w hw =>
    by_cases h1 : w 1 = 0
    ·
      have h0 : w 0 ≠ 0 := by
        intro h0; apply hw; funext i; fin_cases i <;> assumption
      refine ⟨⟨Winf, hWinf⟩, ?_⟩
      rw [basePt, smul_mk, Projectivization.mk_eq_mk_iff']
      refine ⟨(-((v : ℤ) : ZMod q)) * (w 0)⁻¹, ?_⟩
      rw [red_mulVec_basePt]
      funext i
      fin_cases i
      · show (-((v : ℤ) : ZMod q)) * (w 0)⁻¹ * w 0 = ((((Winf 0 1 : ℤ)) : ZMod q))
        rw [mul_assoc, inv_mul_cancel₀ h0, mul_one]
        show _ = (((-v : ℤ)) : ZMod q)
        rw [Int.cast_neg]
      · show (-((v : ℤ) : ZMod q)) * (w 0)⁻¹ * w 1 = ((((Winf 1 1 : ℤ)) : ZMod q))
        rw [h1, mul_zero]
        show (0 : ZMod q) = ((((q : ℕ) : ℤ)) : ZMod q)
        rw [Int.cast_natCast, ZMod.natCast_self]
    ·
      set t : ZMod q := w 0 / w 1 with ht
      refine ⟨Tg N ^ (t.val : ℤ), ?_⟩
      rw [basePt, smul_mk, Projectivization.mk_eq_mk_iff']
      refine ⟨(w 1)⁻¹, ?_⟩
      rw [red_mulVec_basePt]
      have h01 : (((Tg N ^ (t.val : ℤ) : Gamma0 N) : SL(2, ℤ)) 0 1 : ℤ) = (t.val : ℤ) := by
        rw [show (((Tg N ^ (t.val : ℤ) : Gamma0 N) : SL(2, ℤ)) 0 1 : ℤ) =
          ((((Tg N ^ (t.val : ℤ) : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1) from rfl, coe_Tg_zpow]
        rfl
      have h11 : (((Tg N ^ (t.val : ℤ) : Gamma0 N) : SL(2, ℤ)) 1 1 : ℤ) = 1 := by
        rw [show (((Tg N ^ (t.val : ℤ) : Gamma0 N) : SL(2, ℤ)) 1 1 : ℤ) =
          ((((Tg N ^ (t.val : ℤ) : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1) from rfl, coe_Tg_zpow]
        rfl
      rw [h01, h11]
      funext i
      fin_cases i
      · show (w 1)⁻¹ * w 0 = (((t.val : ℤ)) : ZMod q)
        rw [Int.cast_natCast, ZMod.natCast_zmod_val, ht, div_eq_inv_mul]
      · show (w 1)⁻¹ * w 1 = ((1 : ℤ) : ZMod q)
        rw [Int.cast_one, inv_mul_cancel₀ h1]

end Shapiro

section Final

variable (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) (S₀ : Set ℕ) (κ : Type) [Field κ]

include hqN in

theorem final {lam : ℕ → κ} (hτ : IsEigensystemH1 N (rhoP N q κ) (aP q κ) S₀ lam) :
    haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩
    IsEigensystemH1 (N * q) (1 : Representation κ (Gamma0 (N * q)) κ) (fun _ => LinearMap.id) (insert q S₀) lam := by
  classical
  have hq : q.Prime := Fact.out
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) hq.ne_zero⟩
  obtain ⟨x, hx, heig⟩ := hτ
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective _ x
  obtain ⟨y, hy1, hy2⟩ := HeckeEis.exists_addMonoidHom_functional_cocycle_smul_heckeOperatorHom_mul_eq q N
    (rhoP N q κ) (aP q κ) (evb q κ) (fun _ => (1 : κ)) (evb_rhoP N q κ) (evb_aP q κ)
    (z : Gamma0 N → (ProjLine q →₀ κ)) z.2
  obtain ⟨s, hs⟩ := exists_section N q hqN

  have hy0 : y ≠ 0 := by
    intro hy
    apply hx
    rw [coeffH1Mk_eq_zero_iff]
    refine mem_coeffCoboundaries_of_forall_apply_basePt N q κ z.2 s hs fun h hh => ?_

    have hb : (q : ℤ) ∣ (h : SL(2, ℤ)) 0 1 := by
      rw [smul_basePt_eq_iff, red_val, Matrix.map_apply] at hh
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hh

    let u : ↥(heckeUpper N q) := ⟨h, (mem_heckeUpper N q).mpr hb⟩
    have hmem : heckeConjSL N q u ∈ Gamma0 (N * q) := by
      rw [Gamma0_mem]
      show (((heckeConjMat q ((h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 : ℤ) : ZMod (N * q)) = 0
      rw [heckeConjMat_apply_one_zero, ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      have hc : (N : ℤ) ∣ (h : SL(2, ℤ)) 1 0 := by
        have := h.2
        rw [Gamma0_mem] at this
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
      exact mul_dvd_mul_right hc _
    have hrel := hy1 ⟨heckeConjSL N q u, hmem⟩ h (heckeConjMat_mul_alphaMat hb)
    rw [hy, AddMonoidHom.zero_apply] at hrel

    exact hrel.symm

  let zy : Gamma0 (N * q) → κ := fun g => y (Additive.ofMul g)
  have hzy : zy ∈ coeffCocycles (1 : Representation κ (Gamma0 (N * q)) κ) := by
    intro g h
    change y (Additive.ofMul (g * h)) = y (Additive.ofMul g) + y (Additive.ofMul h)
    rw [ofMul_mul, map_add]
  refine ⟨coeffH1Mk _ ⟨zy, hzy⟩, ?_, fun ℓ hℓ hℓNq hℓS => ?_⟩
  · intro h0
    rw [coeffH1Mk_eq_zero_iff] at h0
    obtain ⟨v, hv⟩ := (mem_coeffCoboundaries_iff _ _).mp h0
    apply hy0
    refine AddMonoidHom.ext fun g => ?_
    have := congrFun hv (Additive.toMul g)
    simp only [MonoidHom.one_apply, Module.End.one_apply, sub_self] at this
    change y (Additive.ofMul (Additive.toMul g)) = 0
    exact this.symm
  · haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hℓN : ¬ ℓ ∣ N := fun h => hℓNq (h.mul_right q)
    have hℓq : ℓ ≠ q := fun h => hℓNq (h ▸ dvd_mul_left q N)
    have hℓS' : ℓ ∉ S₀ := fun h => hℓS (Set.mem_insert_of_mem q h)
    have hℓq0 : (ℓ : ZMod q) ≠ 0 := by
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      exact hℓq ((Nat.prime_dvd_prime_iff_eq hq hℓ).mp h).symm
    have hcompat : IsCompat (N * q) ℓ (1 : Representation κ (Gamma0 (N * q)) κ) LinearMap.id := by
      intro u; simp
    refine ⟨heckeH1 hcompat, isCoeffHeckeOnH1_heckeH1 hcompat, ?_⟩
    obtain ⟨T, hT, hTx⟩ := heig ℓ hℓ hℓN hℓS'
    have hTy : heckeOperatorHom (N * q) ℓ κ y = lam ℓ • y := by
      have h := hy2 ℓ hℓ hℓN hℓq (isCompat_P N q κ ℓ hℓq0) (lam ℓ) T hT hTx
      rwa [one_smul] at h
    rw [heckeH1_mk, ← map_smul]
    congr 1
    refine Subtype.ext (funext fun g => ?_)
    change coeffHeckeFun (N * q) ℓ (1 : Representation κ (Gamma0 (N * q)) κ) LinearMap.id
        (fun h => y (Additive.ofMul h)) g = lam ℓ * y (Additive.ofMul g)
    rw [coeffHeckeFun_trivial, hTy, AddMonoidHom.smul_apply, smul_eq_mul]

end Final

end ShapiroInd
p2m_reactivate "P2MW.S_HeckeEis_isEigensystemH1_one_mul_of_isEigensystemH1_ind_comp.ShapiroInd"

theorem solution
    (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) (S₀ : Set ℕ)
    (κ : Type) [Field κ] (lam : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 N
      ((CuspidalType.ind q κ).comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (CongruenceSubgroup.Gamma0 N).subtype))
      (fun ℓ : ℕ =>
        if h : ((ℓ : ZMod q) ≠ 0) then (CuspidalType.ind q κ) (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h))
        else LinearMap.id) S₀ lam) :
    haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩
    HeckeEis.IsEigensystemH1 (N * q) (1 : Representation κ (CongruenceSubgroup.Gamma0 (N * q)) κ) (fun _ => LinearMap.id)
      (insert q S₀) lam :=
  ShapiroInd.final N q hqN S₀ κ hocc

end S_HeckeEis_isEigensystemH1_one_mul_of_isEigensystemH1_ind_comp
end P2MW
export P2MW.S_HeckeEis_isEigensystemH1_one_mul_of_isEigensystemH1_ind_comp (solution)
