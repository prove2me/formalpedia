-- Prove2me | solution 1 for GlobalTheory.LevelLaw.last_steps_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:04:38.913537+00:00
-- url     : https://prove2.me/submissions/3cd173d5-ce2a-443d-ba13-87acab7db479

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ParahoricChainLastTwoStepsRootOfUnity
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_one
import Theorems.Thm_GlobalTheory_SplitWeil_integral_comp_mulVec_eq_smul
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_eq_one_of_valuation_eq_one
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_one
import Theorems.Thm_GlobalTheory_StepData_Chain_ofTwist_laws
import Theorems.Thm_GlobalTheory_StepData_LatFrame_conj_apply
import Theorems.Thm_GlobalTheory_StepData_Level_map_lam
import Theorems.Thm_GlobalTheory_StepData_Level_mem_map
import Theorems.Thm_GlobalTheory_StepData_det_reGL
import Theorems.Thm_GlobalTheory_StepData_exists_diag_blocks
import Theorems.Thm_GlobalTheory_StepData_mem_parahoric
import Theorems.Thm_GlobalTheory_StepData_parahoric_lam
import Theorems.Thm_GlobalTheory_StepData_reGL_val
import Theorems.Thm_GlobalTheory_StepData_tame_det_blocks
import Theorems.Thm_GlobalTheory_StepData_valuation_det_of_mem_KO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
namespace GlobalTheory.LevelLaw
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n]
open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {n : Type} [Fintype n] [DecidableEq n] in
private theorem reGL_mem_KO_of_mem_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b) {g : GL a k} (hg : g ∈ _root_.GlobalTheory.SplitWeil.KO k a) :
    _root_.GlobalTheory.StepData.reGL e g ∈ _root_.GlobalTheory.SplitWeil.KO k b := by
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff, ← map_inv, _root_.GlobalTheory.StepData.reGL_val, _root_.GlobalTheory.StepData.reGL_val]
  obtain ⟨h1, h2⟩ := (_root_.GlobalTheory.SplitFlip.mem_KO_iff _).mp hg
  exact ⟨fun i j => h1 _ _, fun i j => h2 _ _⟩
open MeasureTheory ValuativeRel Matrix in
private theorem exists_pos_pow_eq_one_of_isTame_of_valuation_eq_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {δ : kˣ →* ℂˣ} (hδ : _root_.GlobalTheory.SplitWeil.IsTame δ) {u : kˣ} (hu : valuation k (u : k) = 1) : ∃ n : ℕ, 0 < n ∧ δ u ^ n = 1 := by
  classical
  have hO := Valuation.integer.integers (valuation k)
  let x : 𝒪[k] := ⟨u, by rw [Valuation.mem_integer_iff, hu]⟩
  have hx : IsUnit x := hO.isUnit_iff_valuation_eq_one.mpr hu
  letI := Fintype.ofFinite (IsLocalRing.ResidueField 𝒪[k])
  have hr : IsLocalRing.residue 𝒪[k] x ≠ 0 := (RingHom.isUnit_map _ hx).ne_zero
  have hq : 1 < Fintype.card (IsLocalRing.ResidueField 𝒪[k]) := Fintype.one_lt_card
  refine ⟨Fintype.card (IsLocalRing.ResidueField 𝒪[k]) - 1, by omega, ?_⟩
  have hmem : x ^ (Fintype.card (IsLocalRing.ResidueField 𝒪[k]) - 1) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, map_one, FiniteField.pow_card_sub_one_eq_one _ hr, sub_self]
  have hnu := mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem)
  have hlt := lt_of_le_of_ne (hO.map_le_one _) (mt hO.isUnit_iff_valuation_eq_one.mpr hnu)
  rw [← map_pow]
  apply hδ
  refine lt_of_eq_of_lt ?_ hlt
  simp [x]
  rfl
open MeasureTheory ValuativeRel Matrix in
private theorem hasTypes_apply_mul_left_of_mem_J_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {μ : kˣ →* ℂˣ} {P : _root_.GlobalTheory.StepData.Level (GL a k)} {Q : _root_.GlobalTheory.StepData.Level (GL b k)} {Φ : Matrix b a k → ℂ} (hΦ : _root_.GlobalTheory.StepData.HasTypes μ P Q Φ) {g : GL b k} (hg : g ∈ Q.J) (hgi : g ∈ _root_.GlobalTheory.SplitWeil.KO k b) (B : Matrix b a k) :
    Φ (g.val * B) = ((Q.lam ⟨g, hg⟩ : ℂ) * ((μ (GeneralLinearGroup.det g) : ℂ))⁻¹) * Φ B := by
  have key := congrFun (hΦ.2 ⟨g⁻¹, inv_mem hg⟩) B
  have hn : _root_.GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det g⁻¹) = 1 :=
    _root_.GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one (_root_.GlobalTheory.StepData.valuation_det_of_mem_KO (inv_mem hgi))
  have hl : Q.lam ⟨g⁻¹, inv_mem hg⟩ = (Q.lam ⟨g, hg⟩)⁻¹ := map_inv Q.lam ⟨g, hg⟩
  rw [map_inv] at hn
  simp only [_root_.GlobalTheory.SplitWeil.om, Pi.smul_apply, Units.smul_def, inv_inv, Matrix.mul_one, hl, hn, map_one, Real.one_rpow, Units.val_one, one_mul, map_inv, Units.val_inv_eq_inv_val, Complex.ofReal_one, mul_one, Units.val_one, _root_.GlobalTheory.SplitWeil.nabs_one, smul_eq_mul] at key
  rw [mul_right_comm, ← key, mul_comm, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]
open MeasureTheory ValuativeRel Matrix in
private theorem hasTypes_apply_mul_right_of_mem_J_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {μ : kˣ →* ℂˣ} {P : _root_.GlobalTheory.StepData.Level (GL a k)} {Q : _root_.GlobalTheory.StepData.Level (GL b k)} {Φ : Matrix b a k → ℂ} (hΦ : _root_.GlobalTheory.StepData.HasTypes μ P Q Φ) {g : GL a k} (hg : g ∈ P.J) (hgi : g ∈ _root_.GlobalTheory.SplitWeil.KO k a) (B : Matrix b a k) :
    Φ (B * g.val) = ((P.lam ⟨g, hg⟩ : ℂ) * ((μ (GeneralLinearGroup.det g) : ℂ))⁻¹) * Φ B := by
  have key := congrFun (hΦ.1 ⟨g, hg⟩) B
  have hn : _root_.GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det g) = 1 :=
    _root_.GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one (_root_.GlobalTheory.StepData.valuation_det_of_mem_KO hgi)
  simp only [_root_.GlobalTheory.SplitWeil.om, Pi.smul_apply, Units.smul_def, inv_one, Matrix.one_mul, hn, map_one, Real.one_rpow, Units.val_one, one_mul, inv_one, Complex.ofReal_one, mul_one, _root_.GlobalTheory.SplitWeil.nabs_one, smul_eq_mul] at key
  rw [mul_right_comm, ← key, mul_comm, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]
open MeasureTheory ValuativeRel Matrix in
private theorem withCol_toBlocks11_mul_mulVec_eq_mul_withCol {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] (g : GL (n ⊕ Fin 0) k) (x : Matrix n n' k) (y : n → k) : _root_.GlobalTheory.StepData.withCol (g.val.toBlocks₁₁ * x) (g.val.toBlocks₁₁ *ᵥ y) = g.val * _root_.GlobalTheory.StepData.withCol x y := by
  ext (i | i) (j | j)
  · simp [_root_.GlobalTheory.StepData.withCol, Matrix.mul_apply, Fintype.sum_sum_type, toBlocks₁₁]
  · simp [_root_.GlobalTheory.StepData.withCol, Matrix.mul_apply, Fintype.sum_sum_type, toBlocks₁₁, mulVec, dotProduct]
  · exact i.elim0
  · exact i.elim0
open MeasureTheory ValuativeRel Matrix in
private theorem fromCols_zero_mul_toBlocks11_eq_mul_val {k : Type} [Field k] {n m : Type} [Fintype n] [DecidableEq n] (g : GL (n ⊕ Fin 0) k) (x : Matrix (m ⊕ Unit) n k) :
    (x * g.val.toBlocks₁₁).toRows₁.fromCols 0 = x.toRows₁.fromCols 0 * g.val := by
  ext i (j | j)
  · change _ = ∑ l, (x.toRows₁.fromCols (0 : Matrix m (Fin 0) k)) i l * (g : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k) l (Sum.inl j)
    simp [Matrix.mul_apply, Fintype.sum_sum_type, toRows₁, toBlocks₁₁]
  · exact j.elim0
open MeasureTheory ValuativeRel Matrix in
private theorem mul_apply_inr_unit_eq_vecMul {k : Type} [Field k] {n m : Type} [Fintype n] (x : Matrix (m ⊕ Unit) n k) (B : Matrix n n k) :
    (x * B) (Sum.inr ()) = x (Sum.inr ()) ᵥ* B := by
  funext j
  simp [Matrix.mul_apply, vecMul, dotProduct]
open MeasureTheory ValuativeRel Matrix in
private theorem mulVec_mem_box_of_mem_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] (G : GL n k) (hG : G ∈ _root_.GlobalTheory.SplitWeil.KO k n) (w : kˣ) {m : n → k} (hm : m ∈ _root_.GlobalTheory.StepData.box n w) : (G : Matrix n n k) *ᵥ m ∈ _root_.GlobalTheory.StepData.box n w := by
  rw [_root_.GlobalTheory.StepData.mem_box] at hm ⊢
  intro i
  have hGi := ((_root_.GlobalTheory.SplitFlip.mem_KO_iff G).mp hG).1 i
  refine (Valuation.map_sum_le _ fun j _ => ?_)
  rw [map_mul]
  calc valuation k ((G : Matrix n n k) i j) * valuation k (m j) ≤ 1 * valuation k (m j) := by
        gcongr
        exact (Valuation.mem_integer_iff _ _).mp (hGi j)
    _ ≤ valuation k (w : k) := by rw [one_mul]; exact hm j
open MeasureTheory ValuativeRel Matrix in
private theorem hat_cosetInd_box_vecMul_KO_eq_mulVec {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (ε : k) (G : GL n k) (hG : G ∈ _root_.GlobalTheory.SplitWeil.KO k n) (w : kˣ) (y v : n → k) :
    _root_.GlobalTheory.StepData.hat ψ ν ε (_root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n w) (Submodule.Quotient.mk y)) (v ᵥ* (G : Matrix n n k)) =
      _root_.GlobalTheory.StepData.hat ψ ν ε (_root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n w) (Submodule.Quotient.mk ((G : Matrix n n k) *ᵥ y))) v := by
  have hdet : _root_.GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det G) = 1 :=
    _root_.GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one (_root_.GlobalTheory.StepData.valuation_det_of_mem_KO hG)
  have hiff : ∀ z : n → k, (Submodule.Quotient.mk (p := _root_.GlobalTheory.StepData.box n w) z = Submodule.Quotient.mk y) ↔
      (Submodule.Quotient.mk (p := _root_.GlobalTheory.StepData.box n w) ((G : Matrix n n k) *ᵥ z) = Submodule.Quotient.mk ((G : Matrix n n k) *ᵥ y)) := by
    intro z
    simp only [Submodule.Quotient.eq, ← mulVec_sub]
    refine ⟨mulVec_mem_box_of_mem_KO G hG w, fun h => ?_⟩
    have := mulVec_mem_box_of_mem_KO G⁻¹ (inv_mem hG) w h
    rwa [mulVec_mulVec, Units.inv_mul, one_mulVec] at this
  unfold _root_.GlobalTheory.StepData.hat
  have h := _root_.GlobalTheory.SplitWeil.integral_comp_mulVec_eq_smul ν G (fun z => _root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n w) (Submodule.Quotient.mk ((G : Matrix n n k) *ᵥ y)) z * ((ψ (ε * v ⬝ᵥ z) : Circle) : ℂ))
  rw [hdet, inv_one, one_smul] at h
  rw [← h]
  congr 1
  ext z
  rw [dotProduct_mulVec]
  congr 1
  unfold _root_.GlobalTheory.StepData.cosetInd
  classical
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [← hiff z]
end GlobalTheory.LevelLaw
end
end

set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.LevelLaw
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n]
open MeasureTheory ValuativeRel Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.LevelLaw
namespace _root_.GlobalTheory.LevelLaw
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), _root_.GlobalTheory.SplitWeil.IsUnitVol ν → ∀ (s : ℕ) (κ t : Type) [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t] (δ : kˣ →* ℂˣ) (hδ : _root_.GlobalTheory.SplitWeil.IsTame δ) (η : ℕ → kˣ →* ℂˣ), (∀ j, _root_.GlobalTheory.SplitWeil.IsUnram (η j)) → ∀ g : GL (_root_.GlobalTheory.StepData.XIx κ t (s + 1) ⊕ Fin 0) k, g ∈ ((_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).lev (s + 1) 0 rfl).J → ∃ c : ℂ, (∃ n : ℕ, 0 < n ∧ c ^ n = 1) ∧ (∀ h x₀ y, (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).Psi h (g.val.toBlocks₁₁ * x₀) (g.val.toBlocks₁₁ *ᵥ y) = c * (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).Psi h x₀ y) ∧ ∀ (ψ : AddChar k Circle) (ε : k) (w : kˣ) (y : _root_.GlobalTheory.StepData.XIx κ t (s + 1) → k) x, (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).xiTop (_root_.GlobalTheory.StepData.box _ w) ψ ν ε (Submodule.Quotient.mk y) (x * g.val.toBlocks₁₁) = c * (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).xiTop (_root_.GlobalTheory.StepData.box _ w) ψ ν ε (Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y)) x := by
  intro k _ _ _ _ _ _ ν hν s κ t _ _ _ _ δ hδ η hη g hg
  haveI := hν.1
  set F := _root_.GlobalTheory.StepData.plainFrame (k := k) (_root_.GlobalTheory.StepData.stdOrd κ t (l := s + 1) (s + 1) 0 rfl) with hF
  have hg' : F.conj.symm g ∈ (_root_.GlobalTheory.StepData.parahoric (κ ⊕ Fin (s + 1)) (Fin (s + 1) × t) δ hδ).J :=
    _root_.GlobalTheory.StepData.Level.mem_map.mp hg
  have hgg : g = _root_.GlobalTheory.StepData.reGL F.ord (F.conj.symm g) := by
    have := F.conj_apply (F.conj.symm g)
    rw [MulEquiv.apply_symm_apply] at this
    simpa [hF, _root_.GlobalTheory.StepData.plainFrame] using this
  have hlam : ((_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).lev (s + 1) 0 rfl).lam ⟨g, hg⟩ =
      (_root_.GlobalTheory.StepData.parahoric (κ ⊕ Fin (s + 1)) (Fin (s + 1) × t) δ hδ).lam ⟨F.conj.symm g, hg'⟩ :=
    _root_.GlobalTheory.StepData.Level.map_lam _ _ _
  obtain ⟨hg'int, hg'low⟩ := _root_.GlobalTheory.StepData.mem_parahoric.mp hg'
  obtain ⟨⟨A, hA, hAeq⟩, ⟨D, -, hDeq⟩⟩ := _root_.GlobalTheory.StepData.exists_diag_blocks hg'int hg'low
  have hint : g ∈ _root_.GlobalTheory.SplitWeil.KO k _ := by
    rw [hgg]
    exact reGL_mem_KO_of_mem_KO _ hg'int
  have hdet : GeneralLinearGroup.det g = GeneralLinearGroup.det (F.conj.symm g) := by
    conv_lhs => rw [hgg]
    exact _root_.GlobalTheory.StepData.det_reGL _ _
  have hsplit := _root_.GlobalTheory.StepData.tame_det_blocks hδ hg'int hg'low hAeq hDeq
  have hval := _root_.GlobalTheory.StepData.valuation_det_of_mem_KO hint
  set c : ℂˣ := ((_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).lev (s + 1) 0 rfl).lam ⟨g, hg⟩ *
    (δ (GeneralLinearGroup.det g))⁻¹ with hc
  have hcA : c = (δ (GeneralLinearGroup.det A))⁻¹ := by
    rw [hc, hlam, _root_.GlobalTheory.StepData.parahoric_lam _ D hDeq, hdet, hsplit, _root_.mul_inv_rev, mul_inv_cancel_left]
  have hroot : ∃ n : ℕ, 0 < n ∧ (c : ℂ) ^ n = 1 := by
    obtain ⟨n, hn, hpow⟩ := exists_pos_pow_eq_one_of_isTame_of_valuation_eq_one hδ (_root_.GlobalTheory.StepData.valuation_det_of_mem_KO hA)
    exact ⟨n, hn, by rw [← Units.val_pow_eq_pow_val, hcA, inv_pow, hpow, inv_one, Units.val_one]⟩
  have hL := _root_.GlobalTheory.StepData.Chain.ofTwist_laws δ hδ η hη
    (fun j c h ↦ _root_.GlobalTheory.StepData.plainFrame (_root_.GlobalTheory.StepData.stdOrd κ t j c h))
    (_root_.GlobalTheory.StepData.LatFrame.refl k (_root_.GlobalTheory.StepData.Ix (κ ⊕ Fin (s + 1)) t (s + 2)))
  have hmu : ∀ j, (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).mu j (GeneralLinearGroup.det g) =
      δ (GeneralLinearGroup.det g) := by
    intro j
    change (η j * δ) (GeneralLinearGroup.det g) = _
    rw [MonoidHom.mul_apply, hη j _ hval, one_mul]
  have hΦ := hasTypes_apply_mul_left_of_mem_J_KO (μ := (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).mu (s + 1))
    (Φ := (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).Phi s 0 rfl) (hL.1 s 0 rfl) hg hint
  have hTop := hasTypes_apply_mul_right_of_mem_J_KO (μ := (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).mu (s + 2))
    (Φ := (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).PhiTop) hL.2 hg hint
  rw [hmu] at hΦ hTop
  have hΦ' : ∀ B, (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).Phi s 0 rfl (g.val * B) =
      c * (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).Phi s 0 rfl B := by
    intro B
    rw [hΦ B, hc, Units.val_mul, Units.val_inv_eq_inv_val]
    rfl
  have hTop' : ∀ B, (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).PhiTop (B * g.val) =
      c * (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).PhiTop B := by
    intro B
    rw [hTop B, hc, Units.val_mul, Units.val_inv_eq_inv_val]
    rfl
  obtain ⟨G, hGi, hGeq⟩ : ∃ G : GL (_root_.GlobalTheory.StepData.XIx κ t (s + 1)) k,
      G ∈ _root_.GlobalTheory.SplitWeil.KO k _ ∧ (G : Matrix _ _ k) = g.val.toBlocks₁₁ :=
    ⟨_root_.GlobalTheory.StepData.reGL (Equiv.sumEmpty _ (Fin 0)) g, reGL_mem_KO_of_mem_KO _ hint, by
      rw [_root_.GlobalTheory.StepData.reGL_val]
      rfl⟩
  refine ⟨c, hroot, ?_, ?_⟩
  · intro h x₀ y
    unfold _root_.GlobalTheory.StepData.Chain.Psi
    rw [withCol_toBlocks11_mul_mulVec_eq_mul_withCol]
    simp only [_root_.GlobalTheory.SplitWeil.om, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_assoc]
    rw [hΦ']
    ring
  · intro ψ ε w y x
    unfold _root_.GlobalTheory.StepData.Chain.xiTop
    rw [fromCols_zero_mul_toBlocks11_eq_mul_val, mul_apply_inr_unit_eq_vecMul]
    erw [hTop']
    rw [← hGeq, hat_cosetInd_box_vecMul_KO_eq_mulVec ν ψ ε G hGi w y]
    ring
end _root_.GlobalTheory.LevelLaw
end GlobalTheory.LevelLaw
