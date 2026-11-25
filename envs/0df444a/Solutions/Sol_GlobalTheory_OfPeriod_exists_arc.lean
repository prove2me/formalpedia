-- Prove2me | solution 1 for GlobalTheory.OfPeriod.exists_arc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:07:00.454022+00:00
-- url     : https://prove2.me/submissions/753c0e53-a73a-49bb-8c15-8d6710f0daae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FinrankHomComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpPiIInt
import Theorems.Thm_GlobalTheory_OfPeriod_exp_pi_I_int
import Theorems.Thm_GlobalTheory_AnArc_BwMat_apply
import Theorems.Thm_GlobalTheory_AnArc_Bw_symm
import Theorems.Thm_GlobalTheory_AnArc_div_two_I
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_OfPeriod_apply_imPart
import Theorems.Thm_GlobalTheory_OfPeriod_exists_compl
import Theorems.Thm_GlobalTheory_OfPeriod_exists_imPart
import Theorems.Thm_GlobalTheory_OfPeriod_finrank_hom_complex
import Theorems.Thm_GlobalTheory_OfPeriod_imPart_act
import Theorems.Thm_GlobalTheory_OfPeriod_imPart_eq
import Theorems.Thm_GlobalTheory_OfPeriod_reForm_apply
import Theorems.Thm_GlobalTheory_OfPeriod_sesq_of
import Theorems.Thm_GlobalTheory_OfPeriod_span_intHom
import Theorems.Thm_GlobalTheory_OfPeriod_sub_swap
import Theorems.Thm_GlobalTheory_PolarisedLattice_lattice_of_im
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul
attribute [local simp] GlobalTheory.OfPeriod.reForm_apply



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OfPeriod
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Complex
variable {W : Type} [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W] [FiniteDimensional ℂ W]
  {S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ} {O : Type} [CommRing O] [StarRing O]
  {Y M : Type} [AddCommGroup Y] [Module O Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
  [AddCommGroup M] [Module O M] [Module.Free ℤ M] [Module.Finite ℤ M]
namespace GlobalTheory.OfPeriod
theorem _root_.solution {w : O} (hw : w + star w = 1) (EM : LinearMap.BilinForm ℤ M) (hEM : Function.Bijective EM)
    (P : Y × (Y →+ ℤ) × M →+ W) (hspan : Submodule.span ℝ (Set.range P) = ⊤)
    (hrk : 2 * Module.finrank ℤ Y + Module.finrank ℤ M = 2 * Module.finrank ℂ W)
    (hconj : ∀ z w, starRingEnd ℂ (S z w) = S w z) (hpos : ∀ z, z ≠ 0 → 0 < (S z z).re)
    (hS : ∀ v v', (S (P v) (P v')).im = (v'.2.1 v.1 - v.2.1 v'.1 + EM v.2.2 v'.2.2 : ℤ))
    (ρ : O →+* Module.End ℂ W) (hρ : ∀ a z w, S (ρ a z) w = S z (ρ (star a) w))
    (hP : ∀ (a : O) v, P (a • v.1, v.2.1.comp (DistribSMul.toAddMonoidHom Y (star a)), a • v.2.2) = ρ a (P v))
    (be : LinearMap.BilinForm ℤ Y) (be_symm : ∀ x y, be x y = be y x) (be_pos : ∀ x, x ≠ 0 → 0 < be x x)
    (be_adj : ∀ (a : O) y x, be (a • y) x = be y (star a • x)) (be_even : ∀ x, (2 : ℤ) ∣ be x x)
    (Q : ∀ n : ℕ, (O →+* Module.End ℂ (Fin n → ℂ)) → Prop)
    (hQ : ∀ (U : Type) [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] (σ : O →+* Module.End ℂ U),
      ∃ (n : ℕ) (k : U ≃ₗ[ℂ] (Fin n → ℂ)) (F : O →+* Module.End ℂ (Fin n → ℂ)), Q n F ∧ ∀ a u, k (σ a u) = F a (k u)) :
    ∃ (A : AnArc O) (e : A.X ≃ₗ[O] Y) (f : M ≃+ A.abelian₂) (h : W ≃ₗ[ℂ] A.V),
      (∀ x y, A.be x y = be (e x) (e y)) ∧ (∀ l, A.chi l = (-1) ^ A.Ef (A.FLam w l) l) ∧
      (∀ x, (A.psi x : ℂ) = eTwoPi (A.T x (w • x))) ∧ Q A.gB A.F ∧ (∀ (a : O) m, f (a • m) = A.FLam a (f m)) ∧
      (∀ m m', A.Ef (f m) (f m') = EM m m') ∧ (∀ a z, h (ρ a z) = A.actV a (h z)) ∧
      (∀ v, h (P v) = A.P0 (AnArc.La.mk (e.symm v.1) (v.2.1.comp e.toAddEquiv.toAddMonoidHom) (f v.2.2))) ∧
      (A.BwMat 0).PosDef := by
  have : FiniteDimensional ℝ W := Module.Finite.trans ℂ W
  let R : Submodule ℝ W := Submodule.span ℝ (Set.range fun n => P (0, n, 0))
  have hmem : ∀ n, P (0, n, 0) ∈ R := fun n => Submodule.subset_span ⟨n, rfl⟩
  have hRind : ∀ z, (∀ n, (S z (P (0, n, 0))).im = 0) → ∀ r ∈ R, (S z r).im = 0 := fun z hz r hr =>
    LinearMap.eqOn_span (f := imForm S z) (g := 0) (by rintro _ ⟨n, rfl⟩; exact hz n) hr
  have him : ∀ z z', (S z z').im = -(S z' z).im := fun z z' => by rw [← hconj z z', conj_im, neg_neg]
  have hR : ∀ r ∈ R, ∀ r' ∈ R, (S r r').im = 0 := fun r hr => hRind r fun n => by
    rw [him, hRind _ (fun n' => by simp [hS]) r hr, neg_zero]
  have hρR : ∀ a, ∀ r ∈ R, ρ a r ∈ R := fun a r hr => by
    refine Submodule.span_le (p := R.comap ((ρ a).restrictScalars ℝ)).2 ?_ hr
    rintro _ ⟨n, rfl⟩
    show ρ a (P (0, n, 0)) ∈ R
    rw [← hP]
    simpa using hmem _
  obtain ⟨b, hb, hb'⟩ := exists_imPart hpos hR
  obtain ⟨n, q, j, F, hF, hqj, hj, hdec, hjq, hjF⟩ := exists_compl hpos hb hb' hρ hρR Q hQ
  have hjinj : Function.Injective j := Function.LeftInverse.injective hqj
  have hj' : ∀ z, ∀ r ∈ R, S r (j z) = 0 := fun z r hr => by rw [← hconj, hj z r hr, map_zero]
  have hbR : ∀ r ∈ R, b r = 0 := fun r hr =>
    imPart_eq hpos hb hb' R.zero_mem fun r' hr' => by simp [hR r hr r' hr']
  have hbI : ∀ r ∈ R, b (I • r) = r := fun r hr => imPart_eq hpos hb hb' hr fun r' hr' => by simp
  have hqR : ∀ r ∈ R, q r = 0 := fun r hr => hjinj (by simpa [hbR r hr, hbI r hr] using hdec r)
  have hqρ : ∀ a z, q (ρ a z) = F a (q z) := fun a z => by
    conv_lhs => rw [hdec z]
    simp only [map_add, map_smul, hqR _ (hρR _ _ (hb _)), ← hjF, hqj, smul_zero, zero_add]
  have hSq : ∀ z z', S z (j z') = S (j (q z)) (j z') := fun z z' => by
    conv_lhs => rw [hdec z]
    simp [hj' _ _ (hb _)]
  have hbm : ∀ v : Y × (Y →+ ℤ) × M, v.1 = 0 → b (P v) = 0 := fun v hv =>
    imPart_eq hpos hb hb' R.zero_mem fun r hr => by
      rw [hRind _ (fun n => by simp [hS, hv]) r hr]; simp

  let Φ : W → W → ℂ := fun z z' => S z (b z') - S (j (q z)) (j (q z')) / (2 * I)
  have hΦ : ∀ z z', Φ z z' = Φ z' z - (S z z').im := fun z z' =>
    sub_swap hconj hR hb (hj _) (hj _) (hdec z) (hdec z')
  have hΦρ : ∀ a z z', Φ (ρ a z) z' = Φ z (ρ (star a) z') := fun a z z' => by
    simp only [Φ, hqρ, hjF, hρ, imPart_act hpos hb hb' hρ hρR]
  let s : Y →+ W := P.comp (AddMonoidHom.inl _ _)
  have hs : ∀ y, s y = P (y, 0, 0) := fun _ => rfl
  have hsρ : ∀ (a : O) y, s (a • y) = ρ a (s y) := fun a y => by rw [hs, hs, ← hP]; simp
  let φ : W →ₗ[ℂ] (Y →+ ℂ) :=
    { toFun := fun z => AddMonoidHom.mk' (fun x => Φ z (s x)) fun x x' => by simp only [Φ, map_add]; ring
      map_add' := fun z z' => AddMonoidHom.ext fun x => by simp [Φ]; ring
      map_smul' := fun c z => AddMonoidHom.ext fun x => by simp [Φ]; ring }
  have hφ : ∀ z x, φ z x = Φ z (s x) := fun _ _ => rfl
  have hPv : ∀ v : Y × (Y →+ ℤ) × M, P v = s v.1 + P (0, v.2.1, 0) + P (0, 0, v.2.2) := fun v => by
    rw [hs, ← map_add, ← map_add]; simp
  have hφP : ∀ v x, φ (P v) x = φ (s v.1) x + v.2.1 x - S (j (q (s x))) (j (q (P (0, 0, v.2.2)))) / (2 * I) :=
    fun v x => by
      have h1 : φ (P (0, v.2.1, 0)) x = v.2.1 x := by
        rw [hφ, hΦ, hs, hS]; simp [Φ, hbm, hqR _ (hmem _)]
      have h2 : φ (P (0, 0, v.2.2)) x = -(S (j (q (s x))) (j (q (P (0, 0, v.2.2)))) / (2 * I)) := by
        rw [hφ, hΦ, hs, hS]; simp [Φ, hbm]
      rw [hPv v, map_add, map_add, AddMonoidHom.add_apply, AddMonoidHom.add_apply, h1, h2]; ring
  have hr0 : ∀ r ∈ R, (∀ x, (S (s x) r).im = 0) → r = 0 := fun r hr h0 => by
    have h1 : (imForm S).flip r = 0 := LinearMap.ext_on_range hspan fun v => by
      show (S (P v) r).im = 0
      have h2 := congrArg Complex.re (hb' (P (0, 0, v.2.2)) r hr)
      rw [hbm _ rfl] at h2
      rw [hPv]
      simp only [map_add, LinearMap.add_apply, add_im, h0, hR _ (hmem _) r hr, zero_add]
      simpa using h2.symm
    by_contra hne
    have h3 : (S (I • r) r).im = 0 := congr($h1 (I • r))
    exact (hpos r hne).ne' (by simpa using h3)
  have hbij : Function.Bijective (φ.prod q) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro z hz
      have h1 : q z = 0 := congrArg Prod.snd hz
      have h2 : ∀ x, S z (b (s x)) = 0 := fun x => by
        have : φ z x = 0 := congr(($hz).1 x)
        simpa [hφ, Φ, h1] using this
      have h3 : ∀ x, (S (s x) (b (I • z))).im = 0 ∧ (S (s x) (b z)).im = 0 := fun x => by
        have := h2 x
        rw [hdec z, h1] at this
        simp only [map_add, map_smul, map_zero, add_zero, LinearMap.add_apply, LinearMap.smul_apply,
          apply_imPart hconj hb' _ (hb _), smul_eq_mul] at this
        simpa [Complex.ext_iff] using this
      rw [hdec z, h1, hr0 _ (hb _) fun x => (h3 x).1, hr0 _ (hb _) fun x => (h3 x).2]
      simp
    · rw [← LinearMap.range_eq_top, eq_top_iff]
      rintro ⟨l, z⟩ -
      have h1 : ∀ l : Y →+ ℂ, (l, (0 : Fin n → ℂ)) ∈ LinearMap.range (φ.prod q) := fun l => by
        have : l ∈ (LinearMap.range (φ.prod q)).comap (LinearMap.inl ℂ _ _) := by
          refine (Submodule.span_le.2 ?_) (span_intHom.ge (Submodule.mem_top (x := l)))
          rintro _ ⟨k, rfl⟩
          refine ⟨P (0, k, 0), Prod.ext (AddMonoidHom.ext fun x => ?_) (hqR _ (hmem k))⟩
          show φ _ x = _
          rw [hφP]
          simp [← Prod.zero_eq_mk]
        exact this
      have h2 : (l, z) = (l - φ (j z), 0) + φ.prod q (j z) := by simp [hqj]
      rw [h2]
      exact Submodule.add_mem _ (h1 _) ⟨_, rfl⟩
  let h : W ≃ₗ[ℂ] (Y →+ ℂ) × (Fin n → ℂ) := LinearEquiv.ofBijective _ hbij
  have hrk' : Module.finrank ℤ M = Module.finrank ℝ (Fin n → ℂ) := by
    have : Module.Finite ℂ (Y →+ ℂ) := Module.Finite.equiv (addMonoidHomLequivInt ℂ (A := Y) (B := ℂ)).symm
    have h1 := h.finrank_eq
    rw [Module.finrank_prod, finrank_hom_complex, Module.finrank_fin_fun] at h1
    rw [finrank_real_of_complex, Module.finrank_fin_fun]
    omega
  let SB : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) →ₗ⋆[ℂ] ℂ := (S ∘ₗ j).compl₂ j
  have hSB : ∀ z z', SB z z' = S (j z) (j z') := fun _ _ => rfl
  let Hm : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i k => SB (Pi.single i 1) (Pi.single k 1)
  have hHm : ∀ z z', hermForm Hm z z' = S (j z) (j z') := sesq_of SB
  let p : M →+ (Fin n → ℂ) :=
    q.toAddMonoidHom.comp (P.comp ((AddMonoidHom.inr _ _).comp (AddMonoidHom.inr _ _)))
  have hp : ∀ m, p m = q (P (0, 0, m)) := fun _ => rfl
  have hpE : ∀ m m', (S (j (p m)) (j (p m'))).im = EM m m' := fun m m' => by
    have h1 := hΦ (P (0, 0, m)) (P (0, 0, m'))
    simp only [Φ, hbm (0, 0, _) rfl, map_zero, hS, ← hp, AnArc.div_two_I] at h1
    have h2 := congrArg Complex.re h1
    simp [him (j (p m')) (j (p m))] at h2
    linarith
  have hpF : ∀ (a : O) m, p (a • m) = F a (p m) := fun a m => by
    rw [hp, hp, ← hqρ, ← hP]; simp
  obtain ⟨hpi, hpd, hps⟩ := PolarisedLattice.lattice_of_im EM hEM.1 p (fun z => SB.flip z) hpE hrk'
  let f : M ≃ₗ[ℤ] LinearMap.range p.toIntLinearMap := LinearEquiv.ofInjective p.toIntLinearMap hpi
  have hf : ∀ m, (f m : Fin n → ℂ) = p m := fun _ => rfl
  let Ef := LinearMap.BilinForm.congr f EM
  have hEf : ∀ m m', Ef (f m) (f m') = EM m m' := fun m m' => by
    rw [LinearMap.BilinForm.congr_apply, f.symm_apply_apply, f.symm_apply_apply]
  have hEadj : ∀ (a : O) m m', EM (a • m) m' = EM m (star a • m') := fun a m m' => by
    have : (EM (a • m) m' : ℝ) = EM m (star a • m') := by rw [← hpE, ← hpE, hpF, hpF, hjF, hjF, hρ]
    exact_mod_cast this
  have hEalt : ∀ m m', EM m m' = -EM m' m := fun m m' => by
    have : (EM m m' : ℝ) = -EM m' m := by rw [← hpE, ← hpE, him]
    exact_mod_cast this
  have hTs : ∀ x y, φ (s x) y = φ (s y) x := fun x y => by rw [hφ, hφ, hΦ, hs, hs, hS]; simp
  have hTa : ∀ (a : O) y x, φ (s (a • y)) x = φ (s y) (star a • x) := fun a y x => by
    rw [hφ, hφ, hsρ, hsρ, hΦρ]
  let A : AnArc O :=
    { gB := n
      abelian₂ := LinearMap.range p.toIntLinearMap
      discrete := hpd
      full := hps
      Hm := Hm
      Hm_herm := by ext i k; exact hconj _ _
      Hm_pos := fun z hz => by rw [hHm]; exact hpos _ fun h0 => hz (hjinj (by rw [h0, map_zero]))
      Ef := Ef
      Ef_eq := fun l m => by
        obtain ⟨l, rfl⟩ := f.surjective l
        obtain ⟨m, rfl⟩ := f.surjective m
        rw [hEf, hHm, hf, hf, hpE]
      Ef_bij := by
        have : (Ef : _ → _) = f.symm.dualMap ∘ EM ∘ f.symm := rfl
        rw [this]
        exact f.symm.dualMap.bijective.comp (hEM.comp f.symm.bijective)
      chi := fun l => (-1) ^ EM (w • f.symm l) (f.symm l)
      chi_norm := fun l => by simp
      chi_add := fun l m => by
        obtain ⟨l, rfl⟩ := f.surjective l
        obtain ⟨m, rfl⟩ := f.surjective m
        have h1 : EM (w • (l + m)) (l + m) =
            EM (w • l) l + EM (w • m) m + EM l m + 2 * (EM (w • l) m - EM l m) := by
          have h2 : EM (w • l) m + EM (star w • l) m = EM l m := by
            rw [← LinearMap.add_apply, ← map_add, ← add_smul, hw, one_smul]
          have h3 : EM (w • m) l = -EM (star w • l) m := by rw [hEadj, hEalt]
          simp only [smul_add, map_add, LinearMap.add_apply]
          linarith
        rw [hHm, hf, hf, hpE, exp_pi_I_int, ← map_add f]
        simp only [LinearEquiv.symm_apply_apply, h1, zpow_add₀ (neg_ne_zero.2 (one_ne_zero (α := ℂ))), zpow_mul]
        simp
      chi_neg := fun l => by simp only [map_neg, smul_neg, LinearMap.neg_apply, neg_neg]
      F := F
      F_mem := by rintro a _ ⟨m, rfl⟩; exact ⟨a • m, hpF a m⟩
      F_adj := fun a z z' => by rw [hHm, hHm, hjF, hjF, hρ]
      X := Y
      ct := q.toAddMonoidHom.comp s
      ct_smul := fun a x => by
        show q (s (a • x)) = F a (q (s x))
        rw [hsρ, hqρ]
      T := φ.toAddMonoidHom.comp s
      T_symm := hTs
      T_adj := hTa
      psi := fun x => Units.mk0 (eTwoPi (φ (s x) (w • x))) (AnArc.e_ne_zero _)
      psi_neg := fun x => by simp
      psi_add := fun x y => by
        have h2 : φ (s x) (w • y) + φ (s y) (w • x) = φ (s x) y := by
          rw [hTs y, hTa, ← map_add, ← add_smul, hw, one_smul]
        change eTwoPi _ = eTwoPi _ * eTwoPi _ * eTwoPi (φ (s x) y)
        simp only [← AnArc.e_add, smul_add, map_add, AddMonoidHom.add_apply]
        congr 1
        linear_combination h2
      be := be
      be_symm := be_symm
      be_pos := be_pos
      be_adj := be_adj
      be_even := be_even }
  have hfF : ∀ (a : O) m, f (a • m) = A.FLam a (f m) := fun a m => Subtype.ext (hpF a m)
  refine ⟨A, LinearEquiv.refl O Y, f.toAddEquiv, h, fun _ _ => rfl, fun l => ?_, fun _ => rfl, hF, hfF, hEf,
    fun a z => ?_, fun v => ?_, ?_⟩
  · obtain ⟨l, rfl⟩ := f.surjective l
    rw [← hfF]
    show (-1 : ℂ) ^ EM (w • f.symm (f l)) (f.symm (f l)) = (-1) ^ Ef (f (w • l)) (f l)
    rw [hEf, f.symm_apply_apply]
  · refine Prod.ext (AddMonoidHom.ext fun x => ?_) (hqρ a z)
    show φ (ρ a z) x = φ z (star a • x)
    rw [hφ, hφ, hΦρ, hsρ]
  · refine Prod.ext (AddMonoidHom.ext fun x => ?_) ?_
    · show φ (P v) x = φ (s v.1) x + v.2.1 x - hermForm Hm (q (s x)) (p v.2.2) / (2 * I)
      rw [hφP, hHm, hp]
    · show q (P v) = q (s v.1) + p v.2.2
      rw [hPv, map_add, map_add, hqR _ (hmem _), add_zero, hp]
  · have hB : ∀ y x : Y, A.Bw 0 y x = (S (b (s y)) (b (s x))).re := fun y x => by
      show (φ (s y) x + 0 * (be y x : ℂ) + hermForm Hm (q (s y)) (q (s x)) / (2 * I)).im = _
      rw [hφ, hHm, hb' _ _ (hb _)]
      simp [Φ]
    let c := Module.Free.chooseBasis ℤ A.X
    refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩
    · ext i k; simp [AnArc.BwMat_apply, A.Bw_symm 0 (Module.Free.chooseBasis ℤ A.X i)]
    · have h1 : ∑ i, x i • b (s (c i)) ≠ 0 := fun h0 => hx (funext fun k => by
        have h2 := congrArg (fun z => reForm S z (P (0, (c.coord k).toAddMonoidHom, 0))) h0
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, reForm_apply, hb' _ _ (hmem _), hs,
          hS] at h2
        simpa [Finsupp.single_apply] using h2)
      refine (hpos _ h1).trans_eq ?_
      rw [← reForm_apply]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, reForm_apply, ← hB, dotProduct,
        Matrix.mulVec, AnArc.BwMat_apply, Finset.mul_sum, smul_eq_mul, star_trivial]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by simp only [c]; ring
end GlobalTheory.OfPeriod
