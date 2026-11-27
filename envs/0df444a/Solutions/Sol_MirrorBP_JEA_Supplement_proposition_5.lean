-- Prove2me | solution 1 for MirrorBP.JEA.Supplement.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:23:44.758804+00:00
-- url     : https://prove2.me/submissions/f51ce63b-9f2c-44b8-be8b-6441685e8974

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_SPP
import Definitions.Def_MirrorBP_JEA_Supplement_JPA

open MirrorBP
open MirrorBP.JEA
open MirrorBP.JEA.Supplement

open Finset

theorem solution {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
    (P D : Ty → Finset V) (phi : Ty → ℝ) (c : V → Ty → V → ℝ) (pmin pmax : Ty → ℝ)
    (F : Ty → ℝ → ℝ)
    (hm : 1 < Fintype.card V) (hP : ∀ τ, (P τ).Nonempty) (hD : ∀ τ, (D τ).Nonempty)
    (hrate : IsRate phi) (hcond2 : Condition2 pmin pmax F) (hnorm : JPANormalized pmax c)
    (K : ℕ) :
    (∀ T : ℕ, 0 < T → ∀ π : JPolicy V Ty, AdmissibleJ P D pmin pmax π → ∀ q ∈ StateSpace V K,
        expPayoffJ c F phi π T q / T
          ≤ WsppJ P D F pmin pmax c phi + (Fintype.card V : ℝ) * K / T) ∧
      WstarJ P D pmin pmax c F phi K ≤ WsppJ P D F pmin pmax c phi := by
        classical
        obtain ⟨hphi0, hphi1⟩ := hrate
        -- basic facts
        have hF0 : ∀ τ p, 0 ≤ F τ p := by
          intro τ p
          obtain ⟨h1, hmono, hcont, hl, hr, -⟩ := hcond2 τ
          rw [← hl (min p (pmin τ)) (min_le_right _ _)]
          exact hmono (min_le_left _ _)
        have hF1 : ∀ τ p, F τ p ≤ 1 := by
          intro τ p
          obtain ⟨h1, hmono, hcont, hl, hr, -⟩ := hcond2 τ
          rw [← hr (max p (pmax τ)) (le_max_right _ _)]
          exact hmono (le_max_left _ _)
        have hcN : ∀ j τ k, pmax τ + |c j τ k| ≤ 1 := by
          intro j τ k
          obtain ⟨τ₀, j₀, k₀, τ₁, h1, h2, h3⟩ := hnorm
          linarith [h1 τ, h2 j τ k]
        have hbdd : ∀ τ μ, BddAbove {p | p ∈ Set.Icc (pmin τ) (pmax τ) ∧ F τ p ≤ 1 - μ} := by
          intro τ μ
          exact ⟨pmax τ, fun p hp => hp.1.2⟩
        have hmem : ∀ τ μ, μ ≤ 1 → pmin τ ∈ {p | p ∈ Set.Icc (pmin τ) (pmax τ) ∧ F τ p ≤ 1 - μ} := by
          intro τ μ hμ
          obtain ⟨h1, hmono, hcont, hl, hr, -⟩ := hcond2 τ
          refine ⟨⟨le_rfl, h1.le⟩, ?_⟩
          rw [hl _ le_rfl]; linarith
        have hpp : ∀ τ μ, μ ≤ 1 → pPrice F pmin pmax τ μ ≤ pmax τ := by
          intro τ μ hμ
          exact csSup_le ⟨_, hmem τ μ hμ⟩ (fun p hp => hp.1.2)
        have hanti : ∀ τ μ μ', μ' ≤ μ → μ ≤ 1 → pPrice F pmin pmax τ μ ≤ pPrice F pmin pmax τ μ' := by
          intro τ μ μ' h h1
          refine csSup_le_csSup (hbdd τ μ') ⟨_, hmem τ μ h1⟩ ?_
          intro p hp
          exact ⟨hp.1, by linarith [hp.2]⟩
        have hrdiff : ∀ τ μ μ', 0 ≤ μ' → μ' ≤ μ → μ ≤ 1 →
            revJ F pmin pmax τ μ - revJ F pmin pmax τ μ' ≤ (μ - μ') * pmax τ := by
          intro τ μ μ' h0 h h1
          unfold revJ
          have a1 := mul_le_mul_of_nonneg_left (hanti τ μ μ' h h1) h0
          have a2 := mul_le_mul_of_nonneg_left (hpp τ μ h1) (sub_nonneg.2 h)
          nlinarith
        have hrev : ∀ τ p, p ∈ Set.Icc (pmin τ) (pmax τ) →
            (1 - F τ p) * p ≤ revJ F pmin pmax τ (1 - F τ p) := by
          intro τ p hp
          unfold revJ
          refine mul_le_mul_of_nonneg_left ?_ (by linarith [hF1 τ p])
          exact le_csSup (hbdd τ _) ⟨hp, by linarith⟩
        have hr0 : ∀ τ, revJ F pmin pmax τ 0 = 0 := by
          intro τ; unfold revJ; simp
        -- generic linear functional
        obtain ⟨M, hM⟩ : ∃ M : (V → Ty → V → ℝ) → ((V → Ty → V → ℝ) →ₗ[ℝ] ℝ),
            ∀ G x, M G x = ∑ τ, ∑ j ∈ P τ, ∑ k ∈ D τ, x j τ k * G j τ k := by
          refine ⟨fun G => ⟨⟨fun x => ∑ τ, ∑ j ∈ P τ, ∑ k ∈ D τ, x j τ k * G j τ k, ?_⟩, ?_⟩, ?_⟩
          · intro x y
            simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
          · intro a x
            simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]
          · intro G x; rfl
        obtain ⟨Gn, hGn⟩ : ∃ Gn : V → V → Ty → V → ℝ, ∀ i j τ k, Gn i j τ k =
            phi τ * ((if i = j then 1 else 0) - (if i = k then 1 else 0)) := ⟨_, fun _ _ _ _ => rfl⟩
        have hnet : ∀ i x, netOut P D (fun j τ k => phi τ * x j τ k) {i} = M (Gn i) x := by
          intro i x
          rw [hM]
          unfold netOut
          refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun j _ =>
            Finset.sum_congr rfl fun k _ => ?_
          rw [hGn]
          simp only [Finset.mem_singleton, eq_comm (a := i)]
          ring
        obtain ⟨f, hf⟩ : ∃ f : (V → Ty → V → ℝ) → ℝ, f = sppObjJ P D F pmin pmax c phi := ⟨_, rfl⟩
        have hdiff : ∀ x x' : V → Ty → V → ℝ,
            (∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, 0 ≤ x' j τ k ∧ x' j τ k ≤ x j τ k) →
            (∀ τ, ∑ j ∈ P τ, ∑ k ∈ D τ, x j τ k ≤ 1) →
            f x ≤ f x' + M (fun _ τ _ => phi τ) (x - x') := by
          intro x x' hxx hx1
          rw [hM, hf]
          unfold sppObjJ
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun τ _ => ?_
          have e1 : ∑ j ∈ P τ, ∑ k ∈ D τ, (x - x') j τ k * phi τ
              = phi τ * ∑ j ∈ P τ, ∑ k ∈ D τ, (x j τ k - x' j τ k) := by
            simp only [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
            simp only [Pi.sub_apply]; ring
          rw [e1, ← mul_add]
          refine mul_le_mul_of_nonneg_left ?_ (hphi0 τ)
          have h1 : 0 ≤ ∑ j ∈ P τ, ∑ k ∈ D τ, x' j τ k :=
            Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun k hk => (hxx τ j hj k hk).1
          have h2 : ∑ j ∈ P τ, ∑ k ∈ D τ, x' j τ k ≤ ∑ j ∈ P τ, ∑ k ∈ D τ, x j τ k :=
            Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => (hxx τ j hj k hk).2
          have h3 := hrdiff τ _ _ h1 h2 (hx1 τ)
          have h4 : ∑ j ∈ P τ, ∑ k ∈ D τ, (x j τ k - x' j τ k) * pmax τ
              - (∑ j ∈ P τ, ∑ k ∈ D τ, c j τ k * x j τ k - ∑ j ∈ P τ, ∑ k ∈ D τ, c j τ k * x' j τ k)
              ≤ ∑ j ∈ P τ, ∑ k ∈ D τ, (x j τ k - x' j τ k) := by
            simp only [← Finset.sum_sub_distrib]
            refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => ?_
            have a1 := hcN j τ k
            have a2 := neg_abs_le (c j τ k)
            have a3 := (hxx τ j hj k hk).2
            nlinarith
          have h5 : ∑ j ∈ P τ, ∑ k ∈ D τ, (x j τ k - x' j τ k) * pmax τ
              = (∑ j ∈ P τ, ∑ k ∈ D τ, x j τ k - ∑ j ∈ P τ, ∑ k ∈ D τ, x' j τ k) * pmax τ := by
            simp only [← Finset.sum_mul, Finset.sum_sub_distrib]
          linarith
        have hf0 : f 0 = 0 := by
          rw [hf]; unfold sppObjJ; simp [hr0]
        have hfb : BddAbove (f '' {x | sppFeasX P D phi x}) := by
          refine ⟨1, ?_⟩
          rintro _ ⟨x, hx, rfl⟩
          have h1 := hdiff x 0 (fun τ j hj k hk => ⟨le_rfl, hx.2.2 τ j hj k hk⟩) hx.2.1
          rw [hf0, zero_add, sub_zero, hM] at h1
          refine h1.trans ?_
          rw [← hphi1]
          refine Finset.sum_le_sum fun τ _ => ?_
          simp only [← Finset.sum_mul]
          have := mul_le_mul_of_nonneg_right (hx.2.1 τ) (hphi0 τ)
          linarith
        -- the convex set
        obtain ⟨Z, hZdef⟩ : ∃ Z : Set ((V → Ty → V → ℝ) × ℝ × (V → ℝ)), ∀ e, e ∈ Z ↔
            ((∀ j τ k, 0 ≤ e.1 j τ k) ∧ (∀ τ, ∑ j ∈ P τ, ∑ k ∈ D τ, e.1 j τ k ≤ 1) ∧ e.2.1 ≤ f e.1 ∧
              (∀ i, 0 ≤ e.2.2 i)) := ⟨{e | _}, fun e => Iff.rfl⟩
        have hZ : Convex ℝ Z := by
          intro e he e' he' a b ha hb hab
          rw [hZdef] at he he' ⊢
          obtain ⟨h1, h2, h3, h4⟩ := he
          obtain ⟨h1', h2', h3', h4'⟩ := he'
          have key : ∀ τ, ∑ j ∈ P τ, ∑ k ∈ D τ, (a • e + b • e').1 j τ k
              = a * ∑ j ∈ P τ, ∑ k ∈ D τ, e.1 j τ k + b * ∑ j ∈ P τ, ∑ k ∈ D τ, e'.1 j τ k := by
            intro τ
            simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
              Finset.sum_add_distrib, Finset.mul_sum]
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro j τ k
            have := mul_nonneg ha (h1 j τ k)
            have := mul_nonneg hb (h1' j τ k)
            simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            linarith
          · intro τ
            rw [key]
            have := mul_le_mul_of_nonneg_left (h2 τ) ha
            have := mul_le_mul_of_nonneg_left (h2' τ) hb
            linarith
          · have g1 : a * f e.1 + b * f e'.1 ≤ f (a • e + b • e').1 := by
              rw [hf]
              unfold sppObjJ
              simp only [key]
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
              refine Finset.sum_le_sum fun τ _ => ?_
              obtain ⟨-, -, -, -, -, -, hconc, -⟩ := hcond2 τ
              have q1 := hconc.2
                (x := ∑ j ∈ P τ, ∑ k ∈ D τ, e.1 j τ k)
                ⟨Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => h1 j τ k, h2 τ⟩
                (y := ∑ j ∈ P τ, ∑ k ∈ D τ, e'.1 j τ k)
                ⟨Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => h1' j τ k, h2' τ⟩ ha hb hab
              simp only [smul_eq_mul] at q1
              have q2 : ∑ j ∈ P τ, ∑ k ∈ D τ, c j τ k * (a • e + b • e').1 j τ k
                  = a * ∑ j ∈ P τ, ∑ k ∈ D τ, c j τ k * e.1 j τ k
                    + b * ∑ j ∈ P τ, ∑ k ∈ D τ, c j τ k * e'.1 j τ k := by
                simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
                  Finset.mul_sum, ← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
                ring
              rw [q2]
              have q3 := mul_le_mul_of_nonneg_left q1 (hphi0 τ)
              linarith
            have := mul_le_mul_of_nonneg_left h3 ha
            have := mul_le_mul_of_nonneg_left h3' hb
            simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, smul_eq_mul] at g1 ⊢
            linarith
          · intro i
            have := mul_nonneg ha (h4 i)
            have := mul_nonneg hb (h4' i)
            simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            linarith
        -- evaluation of one-hot sums
        have hev : ∀ τ (q : V → ℕ) (d : Decision V), Feasible P D τ q d → ∀ g : V → V → ℝ,
            ∑ j ∈ P τ, ∑ k ∈ D τ, (if d = some (j, k) then (1 : ℝ) else 0) * g j k
              = d.elim 0 (fun p => g p.1 p.2) := by
          intro τ q d hd g
          rcases d with _ | ⟨j0, k0⟩
          · simp
          · obtain ⟨hj, hk, -⟩ := hd
            rw [Finset.sum_eq_single_of_mem j0 hj, Finset.sum_eq_single_of_mem k0 hk]
            · simp
            · intro k _ hne
              have : ¬ (k0 = k) := fun h => hne h.symm
              simp [this]
            · intro j _ hne
              have : ¬ (j0 = j) := fun h => hne h.symm
              simp [this]
        have hstep : ∀ τ (q : V → ℕ) (d : Decision V), Feasible P D τ q d → ∀ i,
            ((step q d i : ℕ) : ℝ) = q i - d.elim 0 (fun p => (if i = p.1 then 1 else 0) -
              (if i = p.2 then 1 else 0)) := by
          intro τ q d hd i
          rcases d with _ | ⟨j0, k0⟩
          · simp [step]
          · obtain ⟨hj, hk, hq⟩ := hd
            simp only [step, Pi.add_apply, Pi.sub_apply, Option.elim, Pi.single_apply]
            by_cases h1 : i = j0
            · subst h1
              rw [if_pos rfl, if_pos rfl]
              push_cast [Nat.cast_sub (show 1 ≤ q i from hq)]
              ring
            · rw [if_neg h1, if_neg h1]
              push_cast
              simp
        have hstepsum : ∀ τ (q : V → ℕ) (d : Decision V), Feasible P D τ q d →
            ∑ i, ((step q d i : ℕ) : ℝ) = ∑ i, (q i : ℝ) := by
          intro τ q d hd
          rw [Finset.sum_congr rfl (fun i _ => hstep τ q d hd i), Finset.sum_sub_distrib]
          rcases d with _ | ⟨j0, k0⟩ <;> simp
        -- main induction
        have hmain : ∀ π : JPolicy V Ty, AdmissibleJ P D pmin pmax π → ∀ n t h (q : V → ℕ),
            ∃ e ∈ Z, expPayoffFromJ c F phi π n t h q = n * e.2.1 ∧
              ∀ i, (q i : ℝ) - e.2.2 i = n * M (Gn i) e.1 := by
          intro π hπ n
          induction n with
          | zero =>
            intro t h q
            refine ⟨(0, 0, fun i => (q i : ℝ)), ?_, ?_, ?_⟩
            · rw [hZdef]; simp [hf0]
            · simp [expPayoffFromJ]
            · intro i; simp
          | succ n ih =>
            intro t h q
            have hch : ∀ (τ : Ty) (x : Decision V × ℝ), ∃ eT eF, eT ∈ Z ∧ eF ∈ Z ∧
                expPayoffFromJ c F phi π n (t + 1) (h ++ [(q, τ, x.1, x.2, true)]) (step q x.1)
                  = n * eT.2.1 ∧
                expPayoffFromJ c F phi π n (t + 1) (h ++ [(q, τ, x.1, x.2, false)]) q = n * eF.2.1 ∧
                (∀ i, ((step q x.1 i : ℕ) : ℝ) - eT.2.2 i = n * M (Gn i) eT.1) ∧
                (∀ i, (q i : ℝ) - eF.2.2 i = n * M (Gn i) eF.1) := by
              intro τ x
              obtain ⟨eT, h1, h2, h3⟩ := ih (t + 1) (h ++ [(q, τ, x.1, x.2, true)]) (step q x.1)
              obtain ⟨eF, h1', h2', h3'⟩ := ih (t + 1) (h ++ [(q, τ, x.1, x.2, false)]) q
              exact ⟨eT, eF, h1, h1', h2, h2', h3, h3'⟩
            choose eT eF hT hFm hTp hFp hTn hFn using hch
            obtain ⟨a, ha⟩ : ∃ a : Ty → (Decision V × ℝ) → ℝ, ∀ τ x, a τ x = π.act t h q τ x :=
              ⟨_, fun _ _ => rfl⟩
            obtain ⟨A, hA⟩ : ∃ A : Ty → Finset (Decision V × ℝ), ∀ τ, A τ = (π.act t h q τ).support :=
              ⟨_, fun _ => rfl⟩
            have ha0 : ∀ τ x, 0 ≤ a τ x := fun τ x => by rw [ha]; exact π.nonneg t h q τ x
            have ha1 : ∀ τ, ∑ x ∈ A τ, a τ x = 1 := by
              intro τ
              have := π.sum_one t h q τ
              rw [Finsupp.sum] at this
              rw [hA, ← this]
              exact Finset.sum_congr rfl fun x _ => ha τ x
            have hfeas : ∀ τ, ∀ x ∈ A τ, Feasible P D τ q x.1 ∧ x.2 ∈ Set.Icc (pmin τ) (pmax τ) := by
              intro τ x hx
              rw [hA] at hx
              exact hπ t h q τ x hx
            obtain ⟨e', he'⟩ : ∃ e' : (V → Ty → V → ℝ) × ℝ × (V → ℝ), e' = ∑ τ, phi τ • ∑ x ∈ A τ,
              a τ x • ((1 - F τ x.2) • eT τ x + F τ x.2 • eF τ x) := ⟨_, rfl⟩
            have he'Z : e' ∈ Z := by
              rw [he']
              refine hZ.sum_mem (fun τ _ => hphi0 τ) hphi1 fun τ _ => ?_
              refine hZ.sum_mem (fun x _ => ha0 τ x) (ha1 τ) fun x _ => ?_
              exact hZ (hT τ x) (hFm τ x) (by linarith [hF1 τ x.2]) (hF0 τ x.2) (by ring)
            have hlin : ∀ l : ((V → Ty → V → ℝ) × ℝ × (V → ℝ)) →ₗ[ℝ] ℝ, l e' = ∑ τ, phi τ * ∑ x ∈ A τ,
                a τ x * ((1 - F τ x.2) * l (eT τ x) + F τ x.2 * l (eF τ x)) := by
              intro l
              rw [he']
              simp only [map_sum, map_smul, map_add, smul_eq_mul]
            have hv' : e'.2.1 = ∑ τ, phi τ * ∑ x ∈ A τ,
                a τ x * ((1 - F τ x.2) * (eT τ x).2.1 + F τ x.2 * (eF τ x).2.1) :=
              hlin (LinearMap.fst ℝ ℝ (V → ℝ) ∘ₗ LinearMap.snd ℝ (V → Ty → V → ℝ) (ℝ × (V → ℝ)))
            have hQ' : ∀ i, e'.2.2 i = ∑ τ, phi τ * ∑ x ∈ A τ,
                a τ x * ((1 - F τ x.2) * (eT τ x).2.2 i + F τ x.2 * (eF τ x).2.2 i) := fun i =>
              hlin (LinearMap.proj i ∘ₗ LinearMap.snd ℝ ℝ (V → ℝ) ∘ₗ
                LinearMap.snd ℝ (V → Ty → V → ℝ) (ℝ × (V → ℝ)))
            have hN' : ∀ i, M (Gn i) e'.1 = ∑ τ, phi τ * ∑ x ∈ A τ,
                a τ x * ((1 - F τ x.2) * M (Gn i) (eT τ x).1 + F τ x.2 * M (Gn i) (eF τ x).1) := fun i =>
              hlin (M (Gn i) ∘ₗ LinearMap.fst ℝ (V → Ty → V → ℝ) (ℝ × (V → ℝ)))
            -- first step
            obtain ⟨x1, hx1⟩ : ∃ x1 : V → Ty → V → ℝ, ∀ j τ k, x1 j τ k = ∑ x ∈ A τ,
                (a τ x * (1 - F τ x.2)) * (if x.1 = some (j, k) then (1 : ℝ) else 0) :=
              ⟨fun j τ k => ∑ x ∈ A τ,
                (a τ x * (1 - F τ x.2)) * (if x.1 = some (j, k) then (1 : ℝ) else 0), fun _ _ _ => rfl⟩
            have hx1s : ∀ τ (g : V → V → ℝ), ∑ j ∈ P τ, ∑ k ∈ D τ, x1 j τ k * g j k
                = ∑ x ∈ A τ, (a τ x * (1 - F τ x.2)) * x.1.elim 0 (fun p => g p.1 p.2) := by
              intro τ g
              have : ∀ x ∈ A τ, (a τ x * (1 - F τ x.2)) * x.1.elim 0 (fun p => g p.1 p.2)
                  = ∑ j ∈ P τ, ∑ k ∈ D τ, (a τ x * (1 - F τ x.2)) *
                    ((if x.1 = some (j, k) then (1 : ℝ) else 0) * g j k) := by
                intro x hx
                rw [← hev τ q x.1 (hfeas τ x hx).1 g]
                simp only [Finset.mul_sum]
              rw [Finset.sum_congr rfl this]
              symm
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun k _ => ?_
              symm
              rw [hx1, Finset.sum_mul]
              refine Finset.sum_congr rfl fun x _ => ?_
              ring
            obtain ⟨v1, hv1⟩ : ∃ v1 : ℝ, v1 = ∑ τ, phi τ * ∑ x ∈ A τ,
                a τ x * ((1 - F τ x.2) * payJ c τ x.1 x.2) := ⟨_, rfl⟩
            have hx1X : ∀ τ, ∑ j ∈ P τ, ∑ k ∈ D τ, x1 j τ k
                = ∑ x ∈ A τ, a τ x * ((1 - F τ x.2) * x.1.elim 0 (fun _ => 1)) := by
              intro τ
              have := hx1s τ (fun _ _ => 1)
              simp only [mul_one] at this
              rw [this]
              exact Finset.sum_congr rfl fun x _ => by ring
            have helim : ∀ d : Decision V, (0:ℝ) ≤ d.elim 0 (fun _ => 1) ∧
                d.elim 0 (fun _ => (1:ℝ)) ≤ 1 := by
              intro d
              rcases d with _ | p <;> simp
            have hmu : ∀ (τ : Ty) (x : Decision V × ℝ),
                ((1 - F τ x.2) * x.1.elim 0 (fun _ => 1)) ∈ Set.Icc (0:ℝ) 1 := by
              intro τ x
              have h1 := helim x.1
              have h2 := hF0 τ x.2
              have h3 := hF1 τ x.2
              constructor
              · exact mul_nonneg (by linarith) h1.1
              · exact mul_le_one₀ (by linarith) h1.1 h1.2
            have he1Z : ((x1, v1, e'.2.2) : (V → Ty → V → ℝ) × ℝ × (V → ℝ)) ∈ Z := by
              rw [hZdef]
              refine ⟨?_, ?_, ?_, ((hZdef _).1 he'Z).2.2.2⟩
              · intro j τ k
                show 0 ≤ x1 j τ k
                rw [hx1]
                refine Finset.sum_nonneg fun x _ => ?_
                refine mul_nonneg (mul_nonneg (ha0 τ x) (by linarith [hF1 τ x.2])) ?_
                split_ifs <;> norm_num
              · intro τ
                show ∑ j ∈ P τ, ∑ k ∈ D τ, x1 j τ k ≤ 1
                rw [hx1X]
                refine le_trans ?_ (ha1 τ).le
                refine Finset.sum_le_sum fun x _ => ?_
                exact mul_le_of_le_one_right (ha0 τ x) (hmu τ x).2
              · show v1 ≤ f x1
                rw [hv1, hf]
                unfold sppObjJ
                refine Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left ?_ (hphi0 τ)
                obtain ⟨-, -, -, -, -, -, hconc, -⟩ := hcond2 τ
                have jen := hconc.le_map_sum (t := A τ) (w := a τ)
                  (p := fun x => (1 - F τ x.2) * x.1.elim 0 (fun _ => 1))
                  (fun x _ => ha0 τ x) (ha1 τ) (fun x _ => hmu τ x)
                simp only [smul_eq_mul] at jen
                rw [hx1X]
                have hc : ∑ j ∈ P τ, ∑ k ∈ D τ, c j τ k * x1 j τ k
                    = ∑ x ∈ A τ, (a τ x * (1 - F τ x.2)) * x.1.elim 0 (fun p => c p.1 τ p.2) := by
                  rw [← hx1s τ (fun j k => c j τ k)]
                  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => mul_comm _ _
                rw [hc]
                refine le_trans ?_ (sub_le_sub_right jen _)
                rw [← Finset.sum_sub_distrib]
                refine Finset.sum_le_sum fun x hx => ?_
                have hx2 := hrev τ x.2 (hfeas τ x hx).2
                have hgoal : (1 - F τ x.2) * payJ c τ x.1 x.2 ≤
                    revJ F pmin pmax τ ((1 - F τ x.2) * x.1.elim 0 (fun _ => 1)) -
                    (1 - F τ x.2) * x.1.elim 0 (fun p => c p.1 τ p.2) := by
                  obtain ⟨d, p⟩ := x
                  rcases d with _ | ⟨j0, k0⟩
                  · simp [payJ, hr0]
                  · simp only [payJ, Option.elim, mul_one] at hx2 ⊢
                    linarith
                have := mul_le_mul_of_nonneg_left hgoal (ha0 τ x)
                linarith
            have hN1 : ∀ i, M (Gn i) x1 = ∑ τ, phi τ * ∑ x ∈ A τ, (a τ x * (1 - F τ x.2)) *
                x.1.elim 0 (fun p => (if i = p.1 then (1:ℝ) else 0) - (if i = p.2 then 1 else 0)) := by
              intro i
              rw [hM]
              refine Finset.sum_congr rfl fun τ _ => ?_
              rw [← hx1s τ (fun j k => (if i = j then (1:ℝ) else 0) - (if i = k then 1 else 0))]
              simp only [Finset.mul_sum, hGn]
              refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
              ring
            have hn1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
            refine ⟨(1 / ((n:ℝ) + 1)) • (x1, v1, e'.2.2) + ((n:ℝ) / ((n:ℝ) + 1)) • e', ?_, ?_, ?_⟩
            · exact hZ he1Z he'Z (by positivity) (by positivity) (by field_simp; ring)
            · have : ((n + 1 : ℕ) : ℝ) * ((1 / ((n:ℝ) + 1)) • (x1, v1, e'.2.2) +
                  ((n:ℝ) / ((n:ℝ) + 1)) • e').2.1 = v1 + n * e'.2.1 := by
                simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
                push_cast
                field_simp
              rw [this, hv1, hv', Finset.mul_sum, ← Finset.sum_add_distrib]
              rw [expPayoffFromJ]
              refine Finset.sum_congr rfl fun τ _ => ?_
              rw [Finsupp.sum, ← hA]
              rw [mul_left_comm, ← mul_add]
              congr 1
              rw [Finset.mul_sum, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [hTp, hFp, ← ha]
              ring
            · intro i
              have e1 : ((n + 1 : ℕ) : ℝ) * M (Gn i) ((1 / ((n:ℝ) + 1)) • (x1, v1, e'.2.2) +
                  ((n:ℝ) / ((n:ℝ) + 1)) • e').1 = M (Gn i) x1 + n * M (Gn i) e'.1 := by
                simp only [Prod.fst_add, Prod.smul_fst, map_add, map_smul, smul_eq_mul]
                push_cast
                field_simp
              have e2 : ((1 / ((n:ℝ) + 1)) • ((x1, v1, e'.2.2) : (V → Ty → V → ℝ) × ℝ × (V → ℝ)) +
                  ((n:ℝ) / ((n:ℝ) + 1)) • e').2.2 i = e'.2.2 i := by
                simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
                field_simp
                ring
              rw [e1, e2, hN1, hN', hQ']
              have e3 : (q i : ℝ) = ∑ τ, phi τ * ∑ x ∈ A τ, a τ x * (q i : ℝ) := by
                simp only [← Finset.sum_mul, ha1, hphi1, one_mul]
              rw [e3, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun τ _ => ?_
              rw [mul_left_comm, ← mul_add, ← mul_sub]
              congr 1
              rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun x hx => ?_
              have g1 := hTn τ x i
              have g2 := hFn τ x i
              rw [hstep τ q x.1 (hfeas τ x hx).1 i] at g1
              linear_combination (a τ x * (1 - F τ x.2)) * g1 + (a τ x * F τ x.2) * g2
        -- decycling
        have hdecyc : ∀ x : V → Ty → V → ℝ, (∀ j τ k, 0 ≤ x j τ k) →
            (∀ τ, ∑ j ∈ P τ, ∑ k ∈ D τ, x j τ k ≤ 1) → ∃ x', sppFeasX P D phi x' ∧
            ∃ y : V → ℝ, (∀ i, 0 ≤ y i ∧ y i ≤ Fintype.card V) ∧
              f x ≤ f x' + ∑ i, y i * M (Gn i) x := by
          intro x hx0 hx1
          have hcont : ∀ G, Continuous (M G) := fun G => LinearMap.continuous_of_finiteDimensional _
          have hcomp : IsCompact (Set.Icc (0 : V → Ty → V → ℝ) x ∩ ⋂ i, {z | M (Gn i) z = 0}) := by
            refine isCompact_Icc.inter_right ?_
            exact isClosed_iInter fun i => isClosed_eq (hcont _) continuous_const
          have hx0' : (0 : V → Ty → V → ℝ) ≤ x := fun j τ k => hx0 j τ k
          obtain ⟨x', hx', hmax⟩ := hcomp.exists_isMaxOn
            ⟨0, ⟨le_rfl, hx0'⟩, by simp⟩ (hcont (fun _ τ _ => phi τ)).continuousOn
          obtain ⟨⟨hx'0, hx'x⟩, hx'n⟩ := hx'
          have hx'n : ∀ i, M (Gn i) x' = 0 := by simpa using hx'n
          have hmax : ∀ z, 0 ≤ z → z ≤ x → (∀ i, M (Gn i) z = 0) →
              M (fun _ τ _ => phi τ) z ≤ M (fun _ τ _ => phi τ) x' := by
            intro z h1 h2 h3
            exact hmax ⟨⟨h1, h2⟩, by simpa using h3⟩
          obtain ⟨R, hR⟩ : ∃ R : V → V → Prop, ∀ j k, R j k ↔
              ∃ τ, j ∈ P τ ∧ k ∈ D τ ∧ 0 < phi τ ∧ x' j τ k < x j τ k := ⟨_, fun _ _ => Iff.rfl⟩
          have hunit : ∀ a b, R a b → ∃ u : V → Ty → V → ℝ, (∀ j τ k, 0 ≤ u j τ k) ∧
              (∀ j τ k, 0 < u j τ k → x' j τ k < x j τ k) ∧
              (∀ i, M (Gn i) u = (if i = a then 1 else 0) - (if i = b then 1 else 0)) ∧
              0 < M (fun _ τ _ => phi τ) u := by
            intro a b hab
            obtain ⟨τ, haP, hbD, hτ, hlt⟩ := (hR a b).1 hab
            have hval : ∀ G : V → Ty → V → ℝ,
                M G (fun j σ k => if j = a ∧ σ = τ ∧ k = b then 1 / phi τ else 0)
                  = G a τ b / phi τ := by
              intro G
              rw [hM, Finset.sum_eq_single_of_mem τ (Finset.mem_univ _),
                Finset.sum_eq_single_of_mem a haP, Finset.sum_eq_single_of_mem b hbD]
              · simp; ring
              · intro k _ hk; simp [hk]
              · intro j _ hj; simp [hj]
              · intro σ _ hσ; simp [hσ]
            refine ⟨fun j σ k => if j = a ∧ σ = τ ∧ k = b then 1 / phi τ else 0, ?_, ?_, ?_, ?_⟩
            · intro j σ k
              dsimp only
              split_ifs
              · positivity
              · exact le_rfl
            · intro j σ k hpos
              dsimp only at hpos
              split_ifs at hpos with hc
              · obtain ⟨rfl, rfl, rfl⟩ := hc; exact hlt
              · exact absurd hpos (lt_irrefl _)
            · intro i
              rw [hval, hGn]
              field_simp
            · rw [hval]; positivity
          have hpath : ∀ a b, Relation.TransGen R a b → ∃ u : V → Ty → V → ℝ, (∀ j τ k, 0 ≤ u j τ k) ∧
              (∀ j τ k, 0 < u j τ k → x' j τ k < x j τ k) ∧
              (∀ i, M (Gn i) u = (if i = a then 1 else 0) - (if i = b then 1 else 0)) ∧
              0 < M (fun _ τ _ => phi τ) u := by
            intro a b hab
            induction hab with
            | single h => exact hunit _ _ h
            | tail _ h ih =>
              obtain ⟨u, u1, u2, u3, u4⟩ := ih
              obtain ⟨w, w1, w2, w3, w4⟩ := hunit _ _ h
              refine ⟨u + w, ?_, ?_, ?_, ?_⟩
              · intro j τ k
                exact add_nonneg (u1 j τ k) (w1 j τ k)
              · intro j τ k hpos
                rcases (u1 j τ k).lt_or_eq with h' | h'
                · exact u2 j τ k h'
                · rcases (w1 j τ k).lt_or_eq with h'' | h''
                  · exact w2 j τ k h''
                  · simp [← h', ← h''] at hpos
              · intro i
                rw [map_add, u3, w3]; ring
              · rw [map_add]; linarith
          have hacyc : ∀ a, ¬ Relation.TransGen R a a := by
            intro a haa
            obtain ⟨u, u1, u2, u3, u4⟩ := hpath a a haa
            have hev : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), ∀ j τ k,
                x' j τ k + ε * u j τ k ≤ x j τ k := by
              refine Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun τ =>
                Filter.eventually_all.2 fun k => ?_
              rcases (u1 j τ k).lt_or_eq with h' | h'
              · have hlt := u2 j τ k h'
                have hc : Continuous (fun ε : ℝ => x' j τ k + ε * u j τ k) := by fun_prop
                have : ∀ᶠ ε : ℝ in nhds 0, x' j τ k + ε * u j τ k < x j τ k :=
                  hc.continuousAt.eventually (Iio_mem_nhds (by simpa using hlt))
                exact (this.filter_mono nhdsWithin_le_nhds).mono fun ε h => h.le
              · refine Filter.Eventually.of_forall fun ε => ?_
                rw [← h']; simpa using hx'x j τ k
            obtain ⟨ε, hε, hεpos⟩ := (hev.and self_mem_nhdsWithin).exists
            have hεpos : 0 < ε := hεpos
            have := hmax (x' + ε • u) (fun j τ k => add_nonneg (hx'0 j τ k)
              (mul_nonneg hεpos.le (u1 j τ k))) (fun j τ k => hε j τ k) (fun i => by
                rw [map_add, map_smul, hx'n, u3]; simp)
            rw [map_add, map_smul, smul_eq_mul] at this
            nlinarith [mul_pos hεpos u4]
          refine ⟨x', ⟨?_, ?_, ?_⟩, fun a => ((univ.filter (fun b => Relation.TransGen R a b)).card : ℝ),
            ?_, ?_⟩
          · intro i; rw [hnet]; exact hx'n i
          · intro τ
            exact (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hx'x j τ k).trans (hx1 τ)
          · intro τ j _ k _; exact hx'0 j τ k
          · intro i
            exact ⟨Nat.cast_nonneg _, Nat.cast_le.2 (Finset.card_le_univ _)⟩
          · have hy : ∀ j k, R j k →
                ((univ.filter (fun b => Relation.TransGen R k b)).card : ℝ) + 1
                  ≤ ((univ.filter (fun b => Relation.TransGen R j b)).card : ℝ) := by
              intro j k hjk
              have : (univ.filter (fun b => Relation.TransGen R k b)).card
                  < (univ.filter (fun b => Relation.TransGen R j b)).card := by
                refine Finset.card_lt_card ?_
                rw [Finset.ssubset_iff_of_subset]
                · exact ⟨k, by simpa using Relation.TransGen.single hjk, by simpa using hacyc k⟩
                · intro b hb
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
                  exact Relation.TransGen.head hjk hb
              exact_mod_cast this
            obtain ⟨y, hydef⟩ : ∃ y : V → ℝ, ∀ a, y a =
                ((univ.filter (fun b => Relation.TransGen R a b)).card : ℝ) := ⟨_, fun _ => rfl⟩
            simp only [← hydef] at hy ⊢
            have h1 := hdiff x x' (fun τ j _ k _ => ⟨hx'0 j τ k, hx'x j τ k⟩) hx1
            refine h1.trans ?_
            have h2 : ∑ i, y i * M (Gn i) x = ∑ i, y i * M (Gn i) (x - x') := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [map_sub, hx'n, sub_zero]
            have h3 : ∑ i, y i * M (Gn i) (x - x') = ∑ τ, ∑ j ∈ P τ, ∑ k ∈ D τ,
                (x - x') j τ k * (phi τ * (y j - y k)) := by
              simp only [hM, Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun τ _ => ?_
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun k _ => ?_
              have : ∀ i, y i * ((x - x') j τ k * Gn i j τ k) = ((x - x') j τ k * phi τ) *
                  ((if i = j then y i else 0) - (if i = k then y i else 0)) := by
                intro i
                rw [hGn]
                split_ifs <;> ring
              simp only [this]
              rw [← Finset.mul_sum, Finset.sum_sub_distrib]
              simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
              ring
            rw [h2, h3, hM]
            refine add_le_add le_rfl ?_
            refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun j hj =>
              Finset.sum_le_sum fun k hk => ?_
            simp only [Pi.sub_apply]
            have hle : x' j τ k ≤ x j τ k := hx'x j τ k
            rcases hle.lt_or_eq with hlt | heq
            · rcases (hphi0 τ).lt_or_eq with hp | hp
              · have := hy j k ((hR j k).2 ⟨τ, hj, hk, hp, hlt⟩)
                refine mul_le_mul_of_nonneg_left ?_ (sub_nonneg.2 hle)
                exact le_mul_of_one_le_right hp.le (by linarith)
              · rw [← hp]; simp
            · rw [heq]; simp
        have hpart1 : ∀ T : ℕ, 0 < T → ∀ π : JPolicy V Ty, AdmissibleJ P D pmin pmax π →
            ∀ q ∈ StateSpace V K, expPayoffJ c F phi π T q / T
                ≤ WsppJ P D F pmin pmax c phi + (Fintype.card V : ℝ) * K / T := by
          intro T hT π hπ q hq
          have hTr : (0:ℝ) < T := by exact_mod_cast hT
          obtain ⟨e, heZ, hpay, hbal⟩ := hmain π hπ T 0 [] q
          obtain ⟨z1, z2, z3, z4⟩ := (hZdef e).1 heZ
          obtain ⟨x', hx', y, hy, hfx⟩ := hdecyc e.1 z1 z2
          have h1 : f x' ≤ WsppJ P D F pmin pmax c phi := by
            unfold WsppJ
            rw [← hf]
            exact le_csSup hfb ⟨x', hx', rfl⟩
          have h2 : ∑ i, y i * M (Gn i) e.1 ≤ (Fintype.card V : ℝ) * K / T := by
            have hK : ∑ i, (q i : ℝ) = K := by
              have : ∑ i, q i = K := hq
              exact_mod_cast this
            rw [le_div_iff₀ hTr, ← hK, Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_le_sum fun i _ => ?_
            have a1 := hbal i
            have a2 := z4 i
            have a3 : y i * M (Gn i) e.1 * T = y i * ((q i : ℝ) - e.2.2 i) := by rw [a1]; ring
            rw [a3]
            have a4 := mul_le_mul_of_nonneg_left (show (q i : ℝ) - e.2.2 i ≤ q i by linarith) (hy i).1
            exact a4.trans (mul_le_mul_of_nonneg_right (hy i).2 (Nat.cast_nonneg _))
          have h3 : expPayoffJ c F phi π T q / T = e.2.1 := by
            unfold expPayoffJ
            rw [hpay]
            field_simp
          rw [h3]
          linarith
        refine ⟨hpart1, ?_⟩
        obtain ⟨π0, hπ0⟩ : ∃ π0 : JPolicy V Ty, ∀ t h q τ, π0.act t h q τ
            = Finsupp.single ((none : Decision V), pmin τ) 1 := by
          refine ⟨⟨fun _ _ _ τ => Finsupp.single ((none : Decision V), pmin τ) 1, ?_, ?_⟩, ?_⟩
          · intro t h q τ x
            rw [Finsupp.single_apply]; split_ifs <;> norm_num
          · intro t h q τ
            rw [Finsupp.sum_single_index]; rfl
          · intro t h q τ; rfl
        have hadm0 : AdmissibleJ P D pmin pmax π0 := by
          intro t h q τ x hx
          rw [hπ0, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hx
          subst hx
          exact ⟨trivial, le_rfl, (hcond2 τ).1.le⟩
        have hpay0 : ∀ n t h q, expPayoffFromJ c F phi π0 n t h q = 0 := by
          intro n
          induction n with
          | zero => intro t h q; rfl
          | succ n ih =>
            intro t h q
            rw [expPayoffFromJ]
            refine Finset.sum_eq_zero fun τ _ => ?_
            rw [hπ0, Finsupp.sum_single_index] <;> simp [ih, payJ]
        obtain ⟨q0, hq0⟩ : ∃ q0 : V → ℕ, q0 ∈ StateSpace V K := by
          have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
          obtain ⟨v⟩ := this
          refine ⟨Pi.single v K, ?_⟩
          simp [StateSpace]
        have hmem0 : ∀ T : ℕ, (0:ℝ) ∈ {x | ∃ π : JPolicy V Ty, AdmissibleJ P D pmin pmax π ∧
            ∃ q ∈ StateSpace V K, x = expPayoffJ c F phi π T q / T} := by
          intro T
          refine ⟨π0, hadm0, q0, hq0, ?_⟩
          unfold expPayoffJ
          rw [hpay0]; simp
        have hub : ∀ T : ℕ, 0 < T → ∀ x ∈ {x | ∃ π : JPolicy V Ty, AdmissibleJ P D pmin pmax π ∧
            ∃ q ∈ StateSpace V K, x = expPayoffJ c F phi π T q / T},
            x ≤ WsppJ P D F pmin pmax c phi + (Fintype.card V : ℝ) * K / T := by
          rintro T hT x ⟨π, hπ, q, hq, rfl⟩
          exact hpart1 T hT π hπ q hq
        have hle : ∀ T : ℕ, 0 < T → WstarTJ P D pmin pmax c F phi K T
            ≤ WsppJ P D F pmin pmax c phi + (Fintype.card V : ℝ) * K / T := by
          intro T hT
          exact csSup_le ⟨_, hmem0 T⟩ (hub T hT)
        have hge : ∀ T : ℕ, 0 < T → 0 ≤ WstarTJ P D pmin pmax c F phi K T := by
          intro T hT
          exact le_csSup ⟨_, hub T hT⟩ (hmem0 T)
        unfold WstarJ
        refine le_of_forall_pos_le_add fun ε hε => ?_
        refine Filter.limsup_le_of_le ?_ ?_
        · refine Filter.IsBoundedUnder.isCoboundedUnder_le ⟨0, ?_⟩
          rw [Filter.eventually_map]
          filter_upwards [Filter.eventually_gt_atTop 0] with T hT using hge T hT
        · have hlim : Filter.Tendsto (fun T : ℕ => (Fintype.card V : ℝ) * K / T) Filter.atTop (nhds 0) :=
            tendsto_const_div_atTop_nhds_zero_nat _
          filter_upwards [Filter.eventually_gt_atTop 0, hlim.eventually (Iio_mem_nhds hε)] with T hT hT2
          have hT2 : (Fintype.card V : ℝ) * K / T < ε := hT2
          linarith [hle T hT]
