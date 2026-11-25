-- Prove2me | solution 1 for GlobalTheory.EvenPull.even_of_square
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:28:13.340714+00:00
-- url     : https://prove2.me/submissions/bb367217-1847-4d0d-9d1c-bcc87eeb14a3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PulledComparisonEven
import Theorems.Thm_GlobalTheory_EvenPull_even_stalk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.EvenPull
namespace GlobalTheory.EvenPull
theorem _root_.solution {T G B T' G' B' : Scheme.{0}} {L : LB G} {M : LB B} {L' : LB G'} {M' : LB B'}
    (hL : L.IsLB) (hM : M.IsLB)
    {f : T ⟶ G} {p : T ⟶ B} {iT : T ⟶ T} {iG : G ⟶ G} {iB : B ⟶ B}
    {f' : T' ⟶ G'} {p' : T' ⟶ B'} {iT' : T' ⟶ T'} {iG' : G' ⟶ G'} {iB' : B' ⟶ B'}
    {Ψ : G' ⟶ G} {Φ : B' ⟶ B} {h : T' ⟶ T}
    (hf : h ≫ f = f' ≫ Ψ) (hp : p' ≫ Φ = h ≫ p) (ih : iT' ≫ h = h ≫ iT)
    (iF : iT ≫ f = f ≫ iG) (iP : iT ≫ p = p ≫ iB) (iF' : iT' ≫ f' = f' ≫ iG') (iP' : iT' ≫ p' = p' ≫ iB')
    (w : LB.Iso (L.pull f) (M.pull p)) (w' : LB.Iso (L'.pull f') (M'.pull p'))
    (wL : LB.Iso L' (L.pull Ψ)) (wM : LB.Iso M' (M.pull Φ))
    (s : LB.Gen (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]))
    (σ : LB.Gen (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]))
    (s' : LB.Gen (LB.LinComb L' (K := Fin 2) ![iG', 𝟙 G'] ![1, -1]))
    (σ' : LB.Gen (LB.LinComb M' (K := Fin 2) ![iB', 𝟙 B'] ![1, -1]))
    (hs : PMaps wL (K := Fin 2) ![iG', 𝟙 G'] ![iG, 𝟙 G] ![1, -1] s' s Ψ)
    (hσ : PMaps wM (K := Fin 2) ![iB', 𝟙 B'] ![iB, 𝟙 B] ![1, -1] σ' σ Φ)
    (sq : ∀ (Z : Scheme.{0}) (r : Z ⟶ T') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι),
      Φ (p' (r z)) ∈ M.U jM → p' (r z) ∈ M'.U jM' → Ψ (f' (r z)) ∈ L.U jL → f' (r z) ∈ L'.U jL' →
      gw wM (r ≫ p') z jM jM' * gw w' r z jM' (fun _ => jL') =
        gw w (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ f') z jL jL')
    (ev : ∀ (jS : Fin 2 → L.ι) (jT : Fin 2 → M.ι),
      LB.Coh L (fun k => f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) jS →
      LB.Coh M (fun k => p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) jT →
      ∀ (V : T.Opens) (h₁ : V ≤ p ⁻¹ᵁ (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]).U jT)
        (h₂ : V ≤ (M.pull p).U (fun _ => jT 1) ⊓ (L.pull f).U (fun _ => jS 1))
        (h₃ : V ≤ iT ⁻¹ᵁ ((M.pull p).U (fun _ => jT 0) ⊓ (L.pull f).U (fun _ => jS 0)))
        (h₄ : V ≤ f ⁻¹ᵁ (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]).U jS),
        res h₁ (pullU p _ (σ.s jT)) * res h₂ (w.s (fun _ => jT 1, fun _ => jS 1)) =
          res h₃ (pullU iT _ (w.s (fun _ => jT 0, fun _ => jS 0))) * res h₄ (pullU f _ (s.s jS)))
    (jS' : Fin 2 → L'.ι) (jT' : Fin 2 → M'.ι)
    (V : T'.Opens) (h₁ : V ≤ p' ⁻¹ᵁ (LB.LinComb M' (K := Fin 2) ![iB', 𝟙 B'] ![1, -1]).U jT')
    (h₂ : V ≤ (M'.pull p').U (fun _ => jT' 1) ⊓ (L'.pull f').U (fun _ => jS' 1))
    (h₃ : V ≤ iT' ⁻¹ᵁ ((M'.pull p').U (fun _ => jT' 0) ⊓ (L'.pull f').U (fun _ => jS' 0)))
    (h₄ : V ≤ f' ⁻¹ᵁ (LB.LinComb L' (K := Fin 2) ![iG', 𝟙 G'] ![1, -1]).U jS') :
    res h₁ (pullU p' _ (σ'.s jT')) * res h₂ (w'.s (fun _ => jT' 1, fun _ => jS' 1)) =
      res h₃ (pullU iT' _ (w'.s (fun _ => jT' 0, fun _ => jS' 0))) * res h₄ (pullU f' _ (s'.s jS')) := by
  refine unit_ext fun z hz => ?_
  obtain ⟨k₁, k₂⟩ := even_stalk w' s' σ' jS' jT' V h₁ h₂ h₃ h₄ (𝟙 T') z hz
  refine k₁.trans (Eq.trans ?_ k₂.symm)
  choose JL hJL using fun χ : T' ⟶ G => exists_chart hL (χ z)
  choose JM hJM using fun χ : T' ⟶ B => exists_chart hM (χ z)
  obtain ⟨jS, hjS, cS⟩ : ∃ jS : Fin 2 → L.ι, (∀ k, (h ≫ f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) z ∈ L.U (jS k)) ∧
      LB.Coh L (fun k => f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) jS :=
    ⟨fun k => JL (h ≫ f ≫ (![iG, 𝟙 G] : Fin 2 → _) k), fun k => hJL _,
      fun a b e => congrArg (fun q => JL (h ≫ q)) e⟩
  obtain ⟨jT, hjT, cT⟩ : ∃ jT : Fin 2 → M.ι, (∀ k, (h ≫ p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) z ∈ M.U (jT k)) ∧
      LB.Coh M (fun k => p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) jT :=
    ⟨fun k => JM (h ≫ p ≫ (![iB, 𝟙 B] : Fin 2 → _) k), fun k => hJM _,
      fun a b e => congrArg (fun q => JM (h ≫ q)) e⟩
  have S0 : (h ≫ f ≫ iG) z ∈ L.U (jS 0) := hjS 0
  have S1 : (h ≫ f) z ∈ L.U (jS 1) := hjS 1
  have T0 : (h ≫ p ≫ iB) z ∈ M.U (jT 0) := hjT 0
  have T1 : (h ≫ p) z ∈ M.U (jT 1) := hjT 1
  have OrbitIntegralProperties : (h ≫ iT ≫ f) z ∈ L.U (jS 0) := by rw [iF]; exact S0
  have T0a : (h ≫ iT ≫ p) z ∈ M.U (jT 0) := by rw [iP]; exact T0
  have S0b : (iT' ≫ f' ≫ Ψ) z ∈ L.U (jS 0) := by rw [← hf, ← Category.assoc, ih, Category.assoc]; exact OrbitIntegralProperties
  have T0b : (iT' ≫ p' ≫ Φ) z ∈ M.U (jT 0) := by rw [hp, ← Category.assoc, ih, Category.assoc]; exact T0a
  have S0c : ((f' ≫ iG') ≫ Ψ) z ∈ L.U (jS 0) := by rw [← iF', Category.assoc]; exact S0b
  have T0c : ((p' ≫ iB') ≫ Φ) z ∈ M.U (jT 0) := by rw [← iP', Category.assoc]; exact T0b
  have TopsChoiceSecondBound : (f' ≫ Ψ) z ∈ L.U (jS 1) := by rw [← hf]; exact S1
  have T1b : (p' ≫ Φ) z ∈ M.U (jT 1) := by rw [hp]; exact T1
  let W : T.Opens := p ⁻¹ᵁ (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]).U jT ⊓
    ((M.pull p).U (fun _ => jT 1) ⊓ (L.pull f).U (fun _ => jS 1)) ⊓
    iT ⁻¹ᵁ ((M.pull p).U (fun _ => jT 0) ⊓ (L.pull f).U (fun _ => jS 0)) ⊓
    f ⁻¹ᵁ (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]).U jS
  have hW : h z ∈ W := ⟨⟨⟨Set.mem_iInter.2 hjT, mem_pull.2 T1, mem_pull.2 S1⟩, mem_pull.2 T0a, mem_pull.2 OrbitIntegralProperties⟩,
    Set.mem_iInter.2 hjS⟩
  have l₁ : W ≤ _ := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have l₂ : W ≤ _ := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have l₃ : W ≤ _ := inf_le_left.trans inf_le_right
  have l₄ : W ≤ _ := inf_le_right
  obtain ⟨n₁, n₂⟩ := even_stalk w s σ jS jT W l₁ l₂ l₃ l₄ h z hW
  have E := n₁.symm.trans ((congrArg (gm h z W) (ev jS jT cS cT W l₁ l₂ l₃ l₄)).trans n₂)
  have A₁ := sq _ (𝟙 T') z (jT 1) (jT' 1) (jS 1) (jS' 1) T1b (mem_pull.1 (h₂ hz).1) TopsChoiceSecondBound (mem_pull.1 (h₂ hz).2)
  have A₀ := sq _ iT' z (jT 0) (jT' 0) (jS 0) (jS' 0) T0b (mem_pull.1 (h₃ hz).1) S0b (mem_pull.1 (h₃ hz).2)
  have Bσ := hσ _ p' z jT jT' (Fin.forall_fin_two.2 ⟨T0c, T1b⟩) (Set.mem_iInter.1 (h₁ hz))
  have Bs := hs _ f' z jS jS' (Fin.forall_fin_two.2 ⟨S0c, TopsChoiceSecondBound⟩) (Set.mem_iInter.1 (h₄ hz))
  rw [Fin.prod_univ_two] at Bσ Bs
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, zpow_one, zpow_neg] at Bσ Bs
  simp only [Category.id_comp] at A₁ ⊢
  rw [iP', iF', ih] at A₀
  rw [hp] at Bσ
  rw [← hf] at Bs
  apply Additive.ofMul.injective
  have e₁ := congrArg Additive.ofMul E
  have e₂ := congrArg Additive.ofMul A₁
  have e₃ := congrArg Additive.ofMul A₀
  have e₄ := congrArg Additive.ofMul Bσ
  have e₅ := congrArg Additive.ofMul Bs
  simp only [ofMul_mul, ofMul_inv] at e₁ e₂ e₃ e₄ e₅ ⊢
  linear_combination (norm := abel) e₁ + e₂ - e₃ - e₄ + e₅
end GlobalTheory.EvenPull
