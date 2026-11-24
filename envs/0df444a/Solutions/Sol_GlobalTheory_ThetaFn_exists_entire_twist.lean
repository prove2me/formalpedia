-- Prove2me | solution 1 for GlobalTheory.ThetaFn.exists_entire_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:31:12.350717+00:00
-- url     : https://prove2.me/submissions/b675415e-4202-4535-8e3c-17644a0b5a3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasAnConstThetaGrpZeroIff
import Theorems.Thm_GlobalTheory_ThetaFn_exAt_mem_twist_chart_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
namespace GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter AppellHumbertTrivial
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
private theorem exists_algChart_mem_source (hL : L.IsLB) (f : Sp ℂ ⟶ A.left) : ∃ i, ⊤ ≤ f ⁻¹ᵁ L.U i := by
  obtain ⟨cover, -, -⟩ := hL
  obtain ⟨a0⟩ : Nonempty (PrimeSpectrum ℂ) := inferInstance
  have hmem : f.base a0 ∈ (⨆ i, L.U i) := by
    rw [cover]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
  refine ⟨i, fun a _ => ?_⟩
  have hsub : a = a0 := Subsingleton.elim (α := PrimeSpectrum ℂ) a a0
  rw [hsub]
  exact hi
private theorem valAt'_unit_ne_zero_cusp_form_evaluations {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ U) (f : Γ(X, U)ˣ) : valAt' y U f.val ≠ 0 := by
  unfold valAt'
  rw [dif_pos h]
  unfold valAt
  exact (Units.map ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (y.appLE U ⊤ h).hom).toMonoidHom f).ne_zero
private theorem valAt'_resG {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {U V : X.Opens} (hVU : V ≤ U)
    (h : ⊤ ≤ y ⁻¹ᵁ V) (f : Γ(X, U)) :
    valAt' y V (X.presheaf.map (homOfLE hVU).op f) = valAt' y U f := by
  have h' : ⊤ ≤ y ⁻¹ᵁ U := fun a ha => hVU (h ha)
  unfold valAt'
  rw [dif_pos h, dif_pos h']
  unfold valAt
  exact congrArg (fun F => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (F.hom f))
    (Scheme.Hom.map_appLE y h (homOfLE hVU).op)
private theorem valAt'_app_eq_valAt'_comp {X Y : Scheme.{0}} (y : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens)
    (f : Γ(Y, U)) : valAt' y (φ ⁻¹ᵁ U) (φ.app U f) = valAt' (y ≫ φ) U f := by
  unfold valAt'
  by_cases h : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ U
  · have h' : ⊤ ≤ y ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [dif_pos h, dif_pos h']
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · have h' : ¬ ⊤ ≤ y ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [dif_neg h, dif_neg h']
private theorem exAt_eq_ex_comp_lift (z : Fin g → ℂ) :
    exAt u p z = (u.ex z).left ≫ (lift (toUnit A ≫ p) (𝟙 A)).left := by
  unfold exAt
  rw [← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc,
    toUnit_unique (u.ex z ≫ toUnit A) (𝟙 _), Category.id_comp]
private theorem exists_ringHom_eq_valAt' {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) :
    ∃ φ : Γ(X, U) →+* ℂ, ∀ f, φ f = valAt' y U f :=
  ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (y.appLE U ⊤ h).hom, fun f => by
    unfold valAt'
    rw [dif_pos h]
    rfl⟩
private theorem preimage_inf_eq_univ {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {U V : X.Opens}
    (h1 : ⊤ ≤ y ⁻¹ᵁ U) (h2 : ⊤ ≤ y ⁻¹ᵁ V) : ⊤ ≤ y ⁻¹ᵁ (U ⊓ V) := by
  intro a ha
  have h1' := h1 ha
  have h2' := h2 ha
  exact ⟨h1', h2'⟩
private theorem mul_zpow_div_zpow_eq_of_factor {v v' G0 G1 f0 f1 f0' f1' : ℂ} (a b : ℤ) (hG0 : G0 ≠ 0) (hG1 : G1 ≠ 0)
    (hf0' : f0' ≠ 0) (hv : v = G0 ^ a * G1 ^ (-b) * v') (h0 : f0 = G0 * f0') (h1 : f1 = G1 * f1') :
    v * f1 ^ b / f0 ^ a = v' * f1' ^ b / f0' ^ a := by
  subst hv h0 h1
  have hinv : G1 ^ (-b) * G1 ^ b = 1 := by
    rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ hG1)]
  rw [div_eq_div_iff (zpow_ne_zero _ (mul_ne_zero hG0 hf0')) (zpow_ne_zero _ hf0'), mul_zpow, mul_zpow]
  linear_combination (G0 ^ a * v' * f1' ^ b * f0' ^ a) * hinv
private theorem ringHom_prod_units_zpow {R : Type} [CommRing R] (φ : R →+* ℂ) {n : ℕ} (v : Fin n → Rˣ)
    (e : Fin n → ℤ) : φ ((∏ k, v k ^ e k : Rˣ) : R) = ∏ k, (φ (v k : R)) ^ e k := by
  have h1 : φ ((∏ k, v k ^ e k : Rˣ) : R) = ((Units.map φ.toMonoidHom (∏ k, v k ^ e k) : ℂˣ) : ℂ) := rfl
  rw [h1, map_prod, Units.coe_prod]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [map_zpow, Units.val_zpow_eq_zpow_val]
  rfl
private theorem valAt'_res_pullU_eq_valAt'_comp {X Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) (ψ : Y ⟶ X) (V : X.Opens)
    {W : Y.Opens} (h : W ≤ ψ ⁻¹ᵁ V) (hy : ⊤ ≤ y ⁻¹ᵁ W) (f : Γ(X, V)ˣ) :
    valAt' y W (res h (pullU ψ V f)).val = valAt' (y ≫ ψ) V f.val := by
  unfold res pullU
  simp only [Units.coe_map]
  erw [valAt'_resG _ h hy, valAt'_app_eq_valAt'_comp]
private theorem valAt'_res_eq {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {U V : X.Opens} (h : V ≤ U)
    (hy : ⊤ ≤ y ⁻¹ᵁ V) (f : Γ(X, U)ˣ) : valAt' y V (res h f).val = valAt' y U f.val := by
  unfold res
  exact valAt'_resG _ h hy _
private theorem valAt'_linComb_g_eq_prod_zpow {X Y : Scheme.{0}} (L : LB X) (F : Fin 2 → (Y ⟶ X)) (ε : Fin 2 → ℤ)
    (i j : (LB.LinComb L F ε).ι) (y : Sp ℂ ⟶ Y)
    (hy : ⊤ ≤ y ⁻¹ᵁ ((LB.LinComb L F ε).U i ⊓ (LB.LinComb L F ε).U j)) :
    valAt' y ((LB.LinComb L F ε).U i ⊓ (LB.LinComb L F ε).U j) ((LB.LinComb L F ε).g i j).val =
      ∏ k, valAt' (y ≫ F k) (L.U (i k) ⊓ L.U (j k)) (L.g (i k) (j k)).val ^ ε k := by
  have hle : ∀ k, (LB.LinComb L F ε).U i ⊓ (LB.LinComb L F ε).U j ≤ F k ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)) :=
    fun k x hx => ⟨Set.mem_iInter.1 hx.1 k, Set.mem_iInter.1 hx.2 k⟩
  have hg : (LB.LinComb L F ε).g i j = ∏ k, res (hle k) (pullU (F k) _ (L.g (i k) (j k))) ^ ε k := rfl
  obtain ⟨φ, hφ⟩ := exists_ringHom_eq_valAt' y _ hy
  rw [← hφ, hg, ringHom_prod_units_zpow]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [hφ, valAt'_res_pullU_eq_valAt'_comp _ _ _ _ hy]
private theorem div_zpow_eq_mul_zpow_neg (x y : ℂ) (a : ℤ) : x / y ^ a = x * y ^ (-a) := by
  rw [zpow_neg, div_eq_mul_inv]
variable {u p} {Hm : Matrix (Fin g) (Fin g) ℂ} {k : ℤ} {Θ : ThetaGrp A L k T} {x : Fin g → ℂ}
end GlobalTheory.ThetaFn
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter AppellHumbertTrivial
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
namespace GlobalTheory.ThetaFn
theorem _root_.solution (hL : L.IsLB) {m : T ⊗ A ⟶ A} {a b : ℤ}
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])) (hα : α.IsGen)
    {w : (Fin g → ℂ) → Fin g → ℂ} (hwd : Differentiable ℂ w)
    (hw : ∀ z, exAt u p z ≫ m.left = (u.ex (w z)).left) :
    ∃ r : (Fin g → ℂ) → ℂ, Differentiable ℂ r ∧ (∀ z, r z ≠ 0) ∧
      ∀ (j : Fin 2 → L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 0) →
        ⊤ ≤ (u.ex (w z)).left ⁻¹ᵁ L.U (j 1) →
        valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, m.left] j) (α.s j).val *
          u.fr (j 1) (w z) ^ b = r z * u.fr (j 0) z ^ a := by
  have hsnd : ∀ z, exAt u p z ≫ (snd T A).left = (u.ex z).left := by
    intro z
    unfold exAt
    rw [← Over.comp_left, lift_snd]
  unfold LB.Gen.IsGen at hα
  obtain ⟨Q, hQ⟩ : ∃ Q : (Fin 2 → L.ι) → (Fin g → ℂ) → ℂ, ∀ j z, Q j z =
      valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, m.left] j) (α.s j).val *
        u.fr (j 1) (w z) ^ b / u.fr (j 0) z ^ a := ⟨_, fun _ _ => rfl⟩
  have compat : ∀ (j j' : Fin 2 → L.ι) z,
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 0) → ⊤ ≤ (u.ex (w z)).left ⁻¹ᵁ L.U (j 1) →
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j' 0) → ⊤ ≤ (u.ex (w z)).left ⁻¹ᵁ L.U (j' 1) →
      Q j z = Q j' z := by
    intro j j' z h0 h1 h0' h1'
    have hc := (exAt_mem_twist_chart_iff u p (hw z) j).2 ⟨h0, h1⟩
    have hc' := (exAt_mem_twist_chart_iff u p (hw z) j').2 ⟨h0', h1'⟩
    have hW := preimage_inf_eq_univ _ hc hc'
    have hW2 : ⊤ ≤ exAt u p z ⁻¹ᵁ ((LB.LinComb L ![(snd T A).left, m.left] ![a, -b]).U j ⊓
        (LB.LinComb L ![(snd T A).left, m.left] ![a, -b]).U j') := hW
    obtain ⟨φ, hφ⟩ := exists_ringHom_eq_valAt' (exAt u p z) _ hW2
    have E := (congrArg (fun v => φ v.val) (hα j j')).trans
      ((congrArg φ (Units.val_mul _ _)).trans (map_mul φ _ _))
    beta_reduce at E
    have Vj := (hφ _).trans (valAt'_res_eq (exAt u p z) inf_le_left hW2 (α.s j))
    have Vj' := (hφ _).trans (valAt'_res_eq (exAt u p z) inf_le_right hW2 (α.s j'))
    have Gv := (hφ _).trans ((valAt'_linComb_g_eq_prod_zpow L _ _ j j' _ hW2).trans (Fin.prod_univ_two _))
    rw [Vj, Vj', Gv] at E
    have hG0eq : valAt' (exAt u p z ≫ ![(snd T A).left, m.left] 0) (L.U (j 0) ⊓ L.U (j' 0))
        (L.g (j 0) (j' 0)).val = valAt' (u.ex z).left (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)).val := by
      rw [Matrix.cons_val_zero, hsnd]
    have hG1eq : valAt' (exAt u p z ≫ ![(snd T A).left, m.left] 1) (L.U (j 1) ⊓ L.U (j' 1))
        (L.g (j 1) (j' 1)).val =
        valAt' (u.ex (w z)).left (L.U (j 1) ⊓ L.U (j' 1)) (L.g (j 1) (j' 1)).val := by
      rw [Matrix.cons_val_one, Matrix.cons_val_zero, hw]
    rw [hG0eq, hG1eq] at E
    have f0 := u.fr_compat (j 0) (j' 0) z (preimage_inf_eq_univ _ h0 h0')
    have f1 := u.fr_compat (j 1) (j' 1) (w z) (preimage_inf_eq_univ _ h1 h1')
    have hG0 := valAt'_unit_ne_zero_cusp_form_evaluations _ _ (preimage_inf_eq_univ _ h0 h0') (L.g (j 0) (j' 0))
    have hG1 := valAt'_unit_ne_zero_cusp_form_evaluations _ _ (preimage_inf_eq_univ _ h1 h1') (L.g (j 1) (j' 1))
    rw [hQ, hQ]
    exact mul_zpow_div_zpow_eq_of_factor a b hG0 hG1 (u.fr_ne _ _ h0') E f0 f1
  have hex : ∀ z, ∃ j : Fin 2 → L.ι,
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 0) ∧ ⊤ ≤ (u.ex (w z)).left ⁻¹ᵁ L.U (j 1) := by
    intro z
    obtain ⟨i0, hi0⟩ := exists_algChart_mem_source hL (u.ex z).left
    obtain ⟨i1, hi1⟩ := exists_algChart_mem_source hL (u.ex (w z)).left
    exact ⟨![i0, i1], hi0, hi1⟩
  choose J hJ0 hJ1 using hex
  refine ⟨fun z => Q (J z) z, ?_, fun z => ?_, fun j z h0 h1 => ?_⟩
  · refine fun z0 => ?_
    have hO : IsOpen {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (J z0 0) ∧
        ⊤ ≤ (u.ex (w z)).left ⁻¹ᵁ L.U (J z0 1)} :=
      (u.hol (L.U (J z0 0)) 0).1.inter ((u.hol (L.U (J z0 1)) 0).1.preimage hwd.continuous)
    have hz0 : z0 ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (J z0 0) ∧
        ⊤ ≤ (u.ex (w z)).left ⁻¹ᵁ L.U (J z0 1)} := ⟨hJ0 z0, hJ1 z0⟩
    have hval : DifferentiableOn ℂ (fun z => valAt' (exAt u p z)
        (LB.wchart L ![(snd T A).left, m.left] (J z0)) (α.s (J z0)).val)
        {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (J z0 0) ∧ ⊤ ≤ (u.ex (w z)).left ⁻¹ᵁ L.U (J z0 1)} := by
      have hfac : ∀ z, valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, m.left] (J z0))
          (α.s (J z0)).val = valAt' (u.ex z).left
            ((lift (toUnit A ≫ p) (𝟙 A)).left ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] (J z0))
            ((lift (toUnit A ≫ p) (𝟙 A)).left.app _ (α.s (J z0)).val) := by
        intro z
        rw [exAt_eq_ex_comp_lift u p z]
        exact (valAt'_app_eq_valAt'_comp _ _ _ _).symm
      simp only [hfac]
      refine (u.hol _ _).2.mono (fun z hz => ?_)
      have hc := (exAt_mem_twist_chart_iff u p (hw z) (J z0)).2 hz
      rw [exAt_eq_ex_comp_lift u p z] at hc
      exact hc
    have hf1 : DifferentiableOn ℂ (fun z => u.fr (J z0 1) (w z) ^ b)
        {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (J z0 0) ∧ ⊤ ≤ (u.ex (w z)).left ⁻¹ᵁ L.U (J z0 1)} :=
      DifferentiableOn.zpow ((u.fr_hol (J z0 1)).comp hwd.differentiableOn (fun z hz => hz.2))
        (Or.inl (fun z hz => u.fr_ne _ _ hz.2))
    have hf0 : DifferentiableOn ℂ (fun z => u.fr (J z0 0) z ^ a)
        {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (J z0 0) ∧ ⊤ ≤ (u.ex (w z)).left ⁻¹ᵁ L.U (J z0 1)} :=
      DifferentiableOn.zpow ((u.fr_hol (J z0 0)).mono (fun z hz => hz.1))
        (Or.inl (fun z hz => u.fr_ne _ _ hz.1))
    have hQd : DifferentiableOn ℂ (Q (J z0))
        {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (J z0 0) ∧ ⊤ ≤ (u.ex (w z)).left ⁻¹ᵁ L.U (J z0 1)} := by
      have hf0' : DifferentiableOn ℂ (fun z => u.fr (J z0 0) z ^ (-a))
          {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (J z0 0) ∧ ⊤ ≤ (u.ex (w z)).left ⁻¹ᵁ L.U (J z0 1)} :=
        DifferentiableOn.zpow ((u.fr_hol (J z0 0)).mono (fun z hz => hz.1))
          (Or.inl (fun z hz => u.fr_ne _ _ hz.1))
      have hd := (hval.mul hf1).mul hf0'
      refine hd.congr (fun z _ => ?_)
      rw [hQ]
      exact div_zpow_eq_mul_zpow_neg _ _ _
    refine (hQd.differentiableAt (hO.mem_nhds hz0)).congr_of_eventuallyEq ?_
    filter_upwards [hO.mem_nhds hz0] with z hz
    exact compat (J z) (J z0) z (hJ0 z) (hJ1 z) hz.1 hz.2
  · show Q (J z) z ≠ 0
    rw [hQ]
    exact div_ne_zero (mul_ne_zero (valAt'_unit_ne_zero_cusp_form_evaluations _ _
      ((exAt_mem_twist_chart_iff u p (hw z) (J z)).2 ⟨hJ0 z, hJ1 z⟩) _)
      (zpow_ne_zero _ (u.fr_ne _ _ (hJ1 z)))) (zpow_ne_zero _ (u.fr_ne _ _ (hJ0 z)))
  · show _ = Q (J z) z * _
    rw [← compat j (J z) z h0 h1 (hJ0 z) (hJ1 z), hQ,
      div_mul_cancel₀ _ (zpow_ne_zero _ (u.fr_ne _ _ h0))]
end GlobalTheory.ThetaFn
