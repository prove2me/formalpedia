-- Prove2me | solution 1 for GlobalTheory.sections_mulPull_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:07:09.316719+00:00
-- url     : https://prove2.me/submissions/d53bc050-a5de-4ae7-8cca-4bdacc64b41d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyEquivPiOfWeights
import Theorems.Thm_GlobalTheory_MulSplit_nonempty_equiv_pi_of_weights
import Theorems.Thm_GlobalTheory_MulSplit_pl_pl
import Theorems.Thm_GlobalTheory_MulSplit_pl_id
import Theorems.Thm_GlobalTheory_MulSplit_pl_mem_Sg
import Theorems.Thm_GlobalTheory_MulSplit_exists_isG
import Theorems.Thm_GlobalTheory_MulSplit_IsG_pow
import Theorems.Thm_GlobalTheory_MulSplit_IsG_pull
import Theorems.Thm_GlobalTheory_MulSplit_IsG_equiv
import Theorems.Thm_GlobalTheory_MulSplit_pl_equiv
import Theorems.Thm_GlobalTheory_MulSplit_Descends_injective
import Theorems.Thm_GlobalTheory_MulSplit_Descends_weight
import Theorems.Thm_GlobalTheory_MulSplit_secM_equiv
import Theorems.Thm_P2M_GlobalTheory_MulSplit_translT_snd__7615715b5518
import Theorems.Thm_GlobalTheory_MulSplit_mulT_fst
import Theorems.Thm_GlobalTheory_MulSplit_mulT_snd
import Theorems.Thm_GlobalTheory_MulSplit_translT_translPt
import Theorems.Thm_GlobalTheory_MulSplit_translT_translT
import Theorems.Thm_GlobalTheory_MulSplit_translPt_one
import Theorems.Thm_GlobalTheory_MulSplit_translT_one
import Theorems.Thm_GlobalTheory_MulSplit_translT_mulT
import Theorems.Thm_GlobalTheory_MulSplit_descends_mulT
import Theorems.Thm_GlobalTheory_MulSplit_pl_inv
import Theorems.Thm_GlobalTheory_CommPairing_translT_fst
import Theorems.Thm_GlobalTheory_CommPairing_weilIs_symm
import Theorems.Thm_GlobalTheory_finite_torsion_of_isFinite_mul
import Theorems.Thm_GlobalTheory_hasEnoughRootsOfUnity_globalSections
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_val_constGen


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open MulSplit
namespace GlobalTheory
theorem _root_.solution :
    (∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ), (n : K) ≠ 0 → ∀ (U : P.A.left.Opens) (f : Γ(P.A.left, (mulA P.A n).left ⁻¹ᵁ U)), (∀ y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A, y ^ n = 1 → ∀ (e : (mulA P.A n).left ⁻¹ᵁ U ≤ ((toUnit P.A ≫ y) * 𝟙 P.A).left ⁻¹ᵁ ((mulA P.A n).left ⁻¹ᵁ U)), (((toUnit P.A ≫ y) * 𝟙 P.A).left.appLE _ _ e).hom f = f) → ∃! g : Γ(P.A.left, U), ((mulA P.A n).left.app U).hom g = f) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ) (x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A), x ^ n = 1 → ∃ (u : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(mulT P.A (baseOver (Spec (CommRingCat.of K))) n ≫ translPt P.A x).left, (snd (baseOver (Spec (CommRingCat.of K))) P.A ^ n).left] ![1, -1])) (ε : ℤ), u.IsGen ∧ (ε = 1 ∨ ε = -1) ∧ ∀ (y : baseOver (Spec (CommRingCat.of K)) ⟶ P.A) (c : Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)ˣ), y ^ n = 1 → WeilIs P.A P.L n x y c → LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ u (translT P.A y).left) (LB.mulGen P.L _ _ _ _ u (constGen P.A P.L (c ^ ε)))) → CharPairSt → WeilSt → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ x : T ⟶ P.A, x ^ k = 1 → WeilIs P.A P.L k x x 1) ∧ (∀ (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k y x c⁻¹) ∧ ∀ (T' : Over S) (h : T' ⟶ T) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom c)) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (q : ℕ), 1 ≤ q → ∀ c : Over.mk t ⟶ P.A, ∃ d : Over.mk t ⟶ P.A, d ^ q = c ∧ ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 3) ![(snd (Over.mk t) P.A).left, (translPt P.A c).left, (translPt P.A d).left] ![(q : ℤ) - 1, 1, -(q : ℤ)]), w.IsGen) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n j : ℕ), (n : K) ≠ 0 → 1 ≤ j → Nonempty (SecM P.A P.L ((n ^ 2 * j : ℕ) : ℤ) (baseOver (Spec (CommRingCat.of K))) ≃ₗ[Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)] ({x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A // x ^ n = 1} → SecM P.A P.L (j : ℤ) (baseOver (Spec (CommRingCat.of K))))) := by
  intro hmul hfin hgal hchi hchar _ _ htw K _ _ P n j hn hj
  haveI := P.isAb.comm
  haveI : NeZero (n : K) := ⟨hn⟩
  haveI : NeZero n := .of_neZero_natCast K
  haveI := (hfin _ P n NeZero.one_le).1
  haveI hF := finite_torsion_of_isFinite_mul K P n
  haveI := hasEnoughRootsOfUnity_globalSections K n hn
  let eK : K ≃+* Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm
  haveI : IsDomain Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) := eK.symm.toMulEquiv.isDomain K
  have hnu : IsUnit (n : Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)) := by
    simpa using (Ne.isUnit hn).map eK
  have hL := P.isLB
  have hD := descends_mulT n (hgal K P n hn)
  have htw' := htw _ P K (𝟙 _)
  specialize hchi K P n
  specialize hchar K P n hn
  obtain ⟨α, hα⟩ := hmul _ P n
  change ∀ q : ℕ, 1 ≤ q → ∀ c : baseOver (Spec (CommRingCat.of K)) ⟶ P.A,
    ∃ d : baseOver (Spec (CommRingCat.of K)) ⟶ P.A, d ^ q = c ∧ ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 3)
      ![(snd (baseOver (Spec (CommRingCat.of K))) P.A).left, (translPt P.A c).left, (translPt P.A d).left]
      ![(q : ℤ) - 1, 1, -(q : ℤ)]), w.IsGen at htw'
  clear hmul hfin hgal htw
  set T := baseOver (Spec (CommRingCat.of K))
  let G : Subgroup (T ⟶ P.A) := (powMonoidHom n).ker
  haveI : Finite G := hF
  have hτ : ∀ x : T ⟶ P.A, (translT P.A x).left ≫ (fst T P.A).left = (fst T P.A).left :=
    CommPairing.translT_fst
  have hττ : ∀ x y : T ⟶ P.A, (translT P.A x).left ≫ (translT P.A y).left = (translT P.A (y * x)).left :=
    fun x y => by rw [← Over.comp_left, translT_translT]
  have hτ1 : (translT P.A (1 : T ⟶ P.A)).left = 𝟙 _ := by rw [translT_one]; rfl
  have hq : (mulT P.A T n).left ≫ (fst T P.A).left = (fst T P.A).left := by
    rw [← Over.comp_left, mulT_fst]
  have hqs : (mulT P.A T n).left ≫ (snd T P.A).left = (snd T P.A ^ n).left := by
    rw [← Over.comp_left, mulT_snd]
  have hτq : ∀ y : {y : T ⟶ P.A // y ^ n = 1},
      (translT P.A y.1).left ≫ (mulT P.A T n).left = (mulT P.A T n).left := fun y => by
    rw [← Over.comp_left, translT_mulT, y.2, translT_one, Category.comp_id]
  let ρ : Representation Γ(T.left, ⊤) G (Vals P.L (fst T P.A).left) :=
    { toFun := fun y => (pl P.L (translT P.A y.1).left (hτ _)).toLinearMap
      map_one' := LinearMap.ext fun v => pl_id (hτ _) hτ1 v
      map_mul' := fun x y => LinearMap.ext fun v =>
        (pl_pl (hτ _) (hτ _) (hτ _) ((hττ x.1 y.1).trans (by rw [_root_.mul_comm]; rfl)) v).symm }

  have hgen : ∀ χ : G →* Γ(T.left, ⊤)ˣ, ∃ (c : T ⟶ P.A) (u : (Vals P.L (fst T P.A).left)ˣ),
      IsG (Finsupp.single (snd T P.A ^ n).left 1 +
        Finsupp.single ((mulT P.A T n).left ≫ (translPt P.A c).left) (-1)) u ∧
      ∀ y : G, pl P.L (translT P.A y.1).left (hτ _) u.val = (χ y).val • u.val := by
    intro χ
    obtain ⟨b, ⟨hb, hbχ⟩, -⟩ := hchar (fun x => χ ⟨x.1, x.2⟩) (fun x y => χ.map_mul ⟨x.1, x.2⟩ ⟨y.1, y.2⟩)
    obtain ⟨t, ε, ht, hε, hc⟩ := hchi b hb
    obtain ⟨u, hu, hv⟩ := exists_isG (p := (fst T P.A).left) hL t ht
    have hu' : IsG (Finsupp.single ((mulT P.A T n).left ≫ (translPt P.A b).left) 1 +
        Finsupp.single (snd T P.A ^ n).left (-1)) u := by
      rw [dv, Fin.sum_univ_two] at hu; exact hu
    have hw : ∀ y : G, pl P.L (translT P.A y.1).left (hτ _) u.val = ((χ y)⁻¹ ^ ε).val • u.val := by
      intro y
      funext i
      have h1 := val_corr i.2.1 (hc y.1 _ y.2 (CommPairing.weilIs_symm hL (hbχ ⟨y.1, y.2⟩))) i.1.2.2
      rw [val_pull i.2.1, val_mul i.2.1, H1.val_constGen, i.2.2] at h1
      rw [Algebra.smul_def, mul_vals, algebraMap_vals, hv, _root_.mul_comm, gs_unit _ _ ⊤ trivial]
      exact (hv _).trans (congrArg Units.val h1)
    rcases hε with rfl | rfl
    · refine ⟨b, u⁻¹, ?_, fun y => ?_⟩
      · convert hu'.inv using 1
        rw [neg_add, ← Finsupp.single_neg, ← Finsupp.single_neg, neg_neg, add_comm]
      · simpa using pl_inv _ (hw y)
    · obtain ⟨x, hx, -⟩ := htw' n NeZero.one_le b⁻¹
      refine ⟨b⁻¹, Units.map (pl P.L (translT P.A x).left (hτ _) : Vals _ _ →* Vals _ _) u, ?_, fun y => ?_⟩
      · convert hu'.pull hL (hτ x) using 1
        rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single, ← hqs]
        simp only [← Over.comp_left]
        rw [← Category.assoc, ← Category.assoc, translT_mulT, Category.assoc, Category.assoc, translT_translPt,
          translT_snd', hx, mul_inv_cancel, translPt_one]
      · show pl P.L _ (hτ _) (pl P.L _ (hτ x) u.val) = (χ y).val • pl P.L _ (hτ x) u.val
        rw [pl_pl _ _ (hτ _) (hττ _ _), _root_.mul_comm x, ← pl_pl (hτ _) (hτ _) (hτ _) (hττ _ _), hw, map_smul]
        simp

  obtain ⟨e₁⟩ := nonempty_equiv_pi_of_weights (N := Sg P.L (fst T P.A).left (Finsupp.single (snd T P.A).left (j : ℤ)))
    n hnu (fun g : G => Subtype.ext g.2) ρ (Sg P.L (fst T P.A).left (Finsupp.single (snd T P.A ^ n).left (j : ℤ)))
    (fun g v hv => pl_mem_Sg hL (hτ _) hv (by
      rw [Finsupp.mapDomain_single, ← hqs, ← Category.assoc, hτq ⟨g.1, g.2⟩])) (fun χ => by
      obtain ⟨c, u, hu, hw⟩ := hgen χ
      obtain ⟨d, -, w, hw'⟩ := htw' j hj c
      obtain ⟨w', hw'', -⟩ := exists_isG (p := (fst T P.A).left) hL w hw'
      obtain ⟨f, hf, hf'⟩ := hD.weight hL hq (fun y => hτ _) hτq
        (D := Finsupp.single (snd T P.A).left ((j : ℤ) - 1) + Finsupp.single (translPt P.A c).left 1)
        (F := Finsupp.single (snd T P.A ^ n).left (j : ℤ)) hu (fun y => χ ⟨y.1, y.2⟩) (fun y => hw ⟨y.1, y.2⟩) (by
          rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single, hqs,
            Finsupp.single_sub, Finsupp.single_neg]
          abel)
      obtain ⟨a₁⟩ := pl_equiv hL (hτ d) (hτ d⁻¹) ((hττ _ _).trans (by rw [inv_mul_cancel, hτ1]))
        ((hττ _ _).trans (by rw [mul_inv_cancel, hτ1])) (D := Finsupp.single (snd T P.A).left (j : ℤ))
        (E := Finsupp.single (translPt P.A d).left (j : ℤ)) (by
          rw [Finsupp.mapDomain_single, ← Over.comp_left, translT_snd'])
      obtain ⟨a₂⟩ := hw''.equiv hL (E := Finsupp.single (translPt P.A d).left (j : ℤ))
        (F := Finsupp.single (snd T P.A).left ((j : ℤ) - 1) + Finsupp.single (translPt P.A c).left 1) (by
          rw [dv, Fin.sum_univ_three]
          show _ + (Finsupp.single (snd T P.A).left ((j : ℤ) - 1) + Finsupp.single (translPt P.A c).left 1 +
            Finsupp.single (translPt P.A d).left (-(j : ℤ))) = _
          rw [Finsupp.single_neg]
          abel)
      refine ⟨f.comp (a₁.trans a₂).toLinearMap, hf.comp (a₁.trans a₂).injective, fun v => Iff.trans ?_ (hf' v)⟩
      exact ⟨fun ⟨x, hx⟩ => ⟨_, hx⟩, fun ⟨x, hx⟩ => ⟨(a₁.trans a₂).symm x, by
        rw [← hx]; exact congrArg f ((a₁.trans a₂).apply_symm_apply x)⟩⟩)

  obtain ⟨u, hu, -⟩ := exists_isG (p := (fst T P.A).left) hL _ (DVR.pullGen_isGen _ _ _ _ hα (snd T P.A).left)
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  obtain ⟨e₂⟩ := (hu.pow hL j).equiv hL (E := Finsupp.single (snd T P.A ^ n).left ((j + 1 : ℕ) : ℤ))
    (F := Finsupp.single (snd T P.A).left ((n ^ 2 * (j + 1) : ℕ) : ℤ)) (by
      rw [dv, Fin.sum_univ_two]
      show _ + (j + 1) • (Finsupp.single ((snd T P.A).left ≫ 𝟙 _) ((n : ℤ) ^ 2) +
        Finsupp.single (snd T P.A ≫ mulA P.A n).left (-1)) = _
      rw [mulA, MonObj.comp_pow, Category.comp_id, Category.comp_id, smul_add, Finsupp.smul_single,
        Finsupp.smul_single, add_left_comm, ← Finsupp.single_add]
      have e₁ : ((j + 1 : ℕ) : ℤ) + (j + 1) • (-1 : ℤ) = 0 := by simp
      have e₂ : (j + 1) • (n : ℤ) ^ 2 = ((n ^ 2 * (j + 1) : ℕ) : ℤ) := by simp; ring
      rw [e₁, e₂, Finsupp.single_zero, add_zero])
  obtain ⟨e₃⟩ := secM_equiv (T := T) hL ((n ^ 2 * (j + 1) : ℕ) : ℤ)
  obtain ⟨e₄⟩ := secM_equiv (T := T) hL ((j + 1 : ℕ) : ℤ)
  exact ⟨e₃.trans (e₂.symm.trans (e₁.trans (LinearEquiv.piCongrRight fun _ => e₄.symm)))⟩
end GlobalTheory
